#!/usr/bin/env python3
"""Constant-binding guard for the Aspis Poseidon2-M31 permutation.

WHY THIS EXISTS

  The Lean formalization proves properties of an in-Lean Poseidon2 permutation
  (`poseidon2Perm`) whose round-constant schedule is a `RoundConstants`
  parameter.  The `Poseidon2Kat.lean` file pins that parameter to a concrete
  instance (`katRC`) transcribed by hand from the deployed Rust primitive
  (`crates/aspis-statement/src/poseidon2.rs`).  A hand transcription can drift:
  a single mistyped nibble in the Lean constants would make the Lean KAT prove
  a statement about a DIFFERENT permutation than the one that ships.

  This tool closes that transcription gap.  The deployed Rust file is the ONE
  source of truth for the permutation constants.  The guard parses the round
  constants (EXTERNAL_INITIAL / INTERNAL / EXTERNAL_FINAL), the partial-round
  diagonal shift schedule, and the sponge domain tags out of BOTH the Rust
  source AND the Lean source, and asserts they are equal element-for-element.
  CI runs it on every push/PR; ANY divergence fails the build.

  It is grep/parse only -- no cargo, lake, or code execution -- so it stays
  green while unrelated work is in flight and needs no toolchain installed.

WHAT IT BINDS (and what it does NOT)

  This checker + the Lean KAT together establish that the Lean permutation and
  the deployed Rust permutation AGREE on:
    * every round constant and the diagonal shift schedule (this checker), and
    * the pinned known-answer test vectors (the Lean KAT, kernel/`native_decide`
      checked).
  That is strong evidence -- but NOT a proof -- that the two permutations are
  the same function on ALL inputs.  Full function-extensional equality
  ("Lean perm = Rust perm everywhere") remains an honest code-correspondence
  residue; see the ledger in `Poseidon2Kat.lean`.

USAGE
    python3 tools/check_poseidon_binding.py

  Exits 0 iff the Lean `katRC` constants and domain tags match the deployed
  Rust ones element-for-element; prints a PASS/FAIL line per check; exits 1 on
  any mismatch.  A mismatch is a real finding: the Lean model and the deployed
  code disagree on a pinned constant.  Do NOT "fix" it by editing whichever
  side is convenient -- investigate which one drifted from the design.
"""

from __future__ import annotations

import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

RUST_POSEIDON = os.path.join(
    REPO_ROOT, "crates", "aspis-statement", "src", "poseidon2.rs"
)
RUST_SPEND = os.path.join(REPO_ROOT, "crates", "aspis-statement", "src", "spend.rs")
LEAN_KAT = os.path.join(
    REPO_ROOT, "AspisFormal", "AspisFormal", "Poseidon2Kat.lean"
)
LEAN_MODEL = os.path.join(
    REPO_ROOT, "AspisFormal", "AspisFormal", "HashMerkleModel.lean"
)


class Report:
    def __init__(self) -> None:
        self._checks: list[tuple[str, str, bool, str]] = []

    def check(self, name: str, ok: bool, detail: str = "") -> None:
        self._checks.append((name, bool(ok), detail))

    def eq(self, name: str, got, want) -> None:
        ok = got == want
        detail = "" if ok else f"got {got!r}, want {want!r}"
        self.check(name, ok, detail)

    def render(self) -> bool:
        all_ok = True
        for name, ok, detail in self._checks:
            all_ok = all_ok and ok
            tag = "PASS" if ok else "FAIL"
            line = f"  [{tag}] {name}"
            if detail:
                line += f"  ({detail})"
            print(line)
        return all_ok


def read(path: str) -> str:
    if not os.path.isfile(path):
        raise SystemExit(f"FATAL: expected source not found: {path}")
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read()


def to_int(token: str) -> int:
    """Parse a hex (0x..) or decimal integer literal, dropping `_` separators."""
    cleaned = token.replace("_", "")
    return int(cleaned, 16) if cleaned.lower().startswith("0x") else int(cleaned)


def hexes(blob: str) -> list[int]:
    """Every integer literal (hex or underscore-grouped decimal) in `blob`."""
    tokens = re.findall(r"0x[0-9a-fA-F_]+|\d[0-9_]*", blob)
    return [to_int(t) for t in tokens]


def strip_lean_comments(text: str) -> str:
    """Remove Lean block comments (`/- ... -/`, incl. `/-!` and `/--`) and line
    comments (`-- ...`) so digits inside prose are never mistaken for constants.
    The permutation constants and domain tags live on comment-free `def` lines,
    so this is a safe, targeted strip."""
    text = re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def slice_between(text: str, start_pat: str, end_pat: str, where: str) -> str:
    m = re.search(start_pat, text)
    if not m:
        raise SystemExit(f"FATAL: start marker {start_pat!r} not found in {where}")
    rest = text[m.end():]
    e = re.search(end_pat, rest)
    if not e:
        raise SystemExit(f"FATAL: end marker {end_pat!r} not found in {where}")
    return rest[: e.start()]


# --------------------------------------------------------------------------
# Rust side: parse the deployed source of truth.
# --------------------------------------------------------------------------
def rust_constants() -> dict:
    src = read(RUST_POSEIDON)
    ext_init = hexes(
        slice_between(src, r"const EXTERNAL_INITIAL[^=]*=\s*\[", r"\n\];",
                      "poseidon2.rs EXTERNAL_INITIAL")
    )
    ext_final = hexes(
        slice_between(src, r"const EXTERNAL_FINAL[^=]*=\s*\[", r"\n\];",
                      "poseidon2.rs EXTERNAL_FINAL")
    )
    internal = hexes(
        slice_between(src, r"const INTERNAL:\s*\[u32;\s*14\]\s*=\s*\[", r"\];",
                      "poseidon2.rs INTERNAL")
    )
    shifts = hexes(
        slice_between(src, r"const INTERNAL_SHIFTS[^=]*=\s*\[", r"\];",
                      "poseidon2.rs INTERNAL_SHIFTS")
    )
    tweak_m = re.search(
        r"MERKLE_NODE_COMPRESSION_V3_TWEAK:\s*M31\s*=\s*M31\(([^)]+)\)", src
    )
    if not tweak_m:
        raise SystemExit("FATAL: MERKLE_NODE_COMPRESSION_V3_TWEAK not found")
    tweak = to_int(tweak_m.group(1))

    spend = read(RUST_SPEND)

    def domain(name: str) -> int:
        m = re.search(rf"{name}:\s*M31\s*=\s*M31\(([^)]+)\)", spend)
        if not m:
            raise SystemExit(f"FATAL: {name} not found in spend.rs")
        return to_int(m.group(1))

    return {
        "ext_init": ext_init,
        "ext_final": ext_final,
        "internal": internal,
        "shifts": shifts,
        "domains": {
            "owner": domain("DOMAIN_OWNER_KEY"),
            "nullifier": domain("DOMAIN_NULLIFIER"),
            "note": domain("DOMAIN_NOTE"),
            "node_tweak": tweak,
        },
    }


# --------------------------------------------------------------------------
# Lean side: parse the transcribed constants that the KAT actually proves about.
# --------------------------------------------------------------------------
def lean_constants() -> dict:
    src = strip_lean_comments(read(LEAN_KAT))
    ext_init = hexes(
        slice_between(src, r"extInit\s*:=", r"intern\s*:=", "Poseidon2Kat.lean extInit")
    )
    intern = hexes(
        slice_between(src, r"intern\s*:=", r"extFinal\s*:=", "Poseidon2Kat.lean intern")
    )
    # extFinal runs to the end of the katRC definition (next top-level `def`).
    ext_final = hexes(
        slice_between(src, r"extFinal\s*:=", r"\ndef ", "Poseidon2Kat.lean extFinal")
    )

    model = strip_lean_comments(read(LEAN_MODEL))

    def dom(name: str) -> int:
        m = re.search(rf"def\s+{name}\s*:\s*F\s*:=\s*(0x[0-9a-fA-F]+|\d+)", model)
        if not m:
            raise SystemExit(f"FATAL: {name} not found in HashMerkleModel.lean")
        return to_int(m.group(1))

    # The partial-round diagonal in `intLinear` is written as literal
    # multipliers 2^shift on lanes 1..15 (`s i * 2^shift`); lane 0 has no
    # multiplier.  Recovering `shift = log2(multiplier)` reproduces the Rust
    # `INTERNAL_SHIFTS[index - 1]` schedule (which is likewise the lanes-1..15
    # schedule, 15 entries).
    int_lin = slice_between(model, r"def intLinear", r"\ndef ",
                            "HashMerkleModel.lean intLinear")
    mults = [int(x) for x in re.findall(r"s\s+\d+\s*\*\s*(\d+)", int_lin)]
    shifts = [m.bit_length() - 1 for m in mults]

    return {
        "ext_init": ext_init,
        "ext_final": ext_final,
        "internal": intern,
        "shifts": shifts,
        "domains": {
            "owner": dom("DOM_OWNER"),
            "nullifier": dom("DOM_NULLIFIER"),
            "note": dom("DOM_NOTE"),
            "node_tweak": dom("NODE_TWEAK"),
        },
    }


def main() -> int:
    print("=" * 74)
    print("Aspis Poseidon2-M31 constant-binding guard")
    print(f"deployed source of truth : {RUST_POSEIDON}")
    print(f"                           {RUST_SPEND}")
    print(f"Lean model               : {LEAN_KAT}")
    print(f"                           {LEAN_MODEL}")
    print("=" * 74)

    rust = rust_constants()
    lean = lean_constants()
    rep = Report()

    # Shapes first, so a length mismatch is a clear, early finding.
    rep.eq("EXTERNAL_INITIAL length (4x16 = 64)", len(rust["ext_init"]), 64)
    rep.eq("EXTERNAL_FINAL length (4x16 = 64)", len(rust["ext_final"]), 64)
    rep.eq("INTERNAL length (14)", len(rust["internal"]), 14)
    rep.eq("Lean extInit length", len(lean["ext_init"]), 64)
    rep.eq("Lean extFinal length", len(lean["ext_final"]), 64)
    rep.eq("Lean intern length", len(lean["internal"]), 14)

    rep.check(
        "EXTERNAL_INITIAL: Rust == Lean (element-for-element)",
        rust["ext_init"] == lean["ext_init"],
        "" if rust["ext_init"] == lean["ext_init"]
        else f"first diff at index {first_diff(rust['ext_init'], lean['ext_init'])}",
    )
    rep.check(
        "EXTERNAL_FINAL: Rust == Lean (element-for-element)",
        rust["ext_final"] == lean["ext_final"],
        "" if rust["ext_final"] == lean["ext_final"]
        else f"first diff at index {first_diff(rust['ext_final'], lean['ext_final'])}",
    )
    rep.check(
        "INTERNAL: Rust == Lean (element-for-element)",
        rust["internal"] == lean["internal"],
        "" if rust["internal"] == lean["internal"]
        else f"first diff at index {first_diff(rust['internal'], lean['internal'])}",
    )
    rep.check(
        "INTERNAL_SHIFTS diagonal schedule: Rust == Lean (2^shift multipliers)",
        rust["shifts"] == lean["shifts"],
        "" if rust["shifts"] == lean["shifts"]
        else f"rust {rust['shifts']} vs lean {lean['shifts']}",
    )

    for tag in ("owner", "nullifier", "note", "node_tweak"):
        rep.eq(f"domain tag {tag}: Rust == Lean",
               lean["domains"][tag], rust["domains"][tag])

    print()
    all_ok = rep.render()
    print("-" * 74)
    if all_ok:
        print("RESULT: PASS -- the Lean `katRC` constants and domain tags are "
              "element-for-element")
        print("        identical to the deployed Rust permutation.  The Lean "
              "KAT therefore proves")
        print("        its statement about the SAME constant schedule that "
              "ships.")
        return 0
    print("RESULT: FAIL -- the Lean model and deployed Rust disagree on a "
          "pinned constant.")
    print("        This is a real finding. Investigate which side drifted; do "
          "NOT paper over it.")
    return 1


def first_diff(a: list, b: list) -> int:
    for i in range(min(len(a), len(b))):
        if a[i] != b[i]:
            return i
    return min(len(a), len(b))


if __name__ == "__main__":
    sys.exit(main())
