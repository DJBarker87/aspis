#!/usr/bin/env python3
"""Single-source-of-truth guard for the Aspis soundness finite parameters.

WHY THIS EXISTS

  A reviewer's fair critique of the formalization is that "the Lean is math
  about the *intended* parameters, not the *deployed* ones": the Lean file,
  the Python second-opinion checker, and the Rust release ledger each hardcode
  their own copies of rate, domain, fiber count, Johnson multiplicity, and the
  agreement cap.  Nothing forced those copies to agree, so a proof about
  (1 + 1/20)*sqrt(1/512) did not, on its own, certify the constant compiled
  into the verifier.

  This tool closes that gap.  `manifests/soundness-params.json` is the ONE
  source of truth.  This guard reads the manifest and then reads the SOURCE of
  each of the three consumers (Rust verifier ledger + descriptor, Python
  checker, Lean formalization), parses the constants they actually contain,
  and asserts every one matches the manifest.  It also re-derives the
  agreement cap from the manifest's own primitives and confirms it equals the
  pinned 6082.  CI runs this on every push/PR; ANY disagreement fails the
  build.  It is grep/parse only -- no cargo, lake, or python execution of the
  consumers -- so it stays green while unrelated protocol work is in flight and
  never needs those toolchains installed.

  Manifest derivation (re-checked below):
    alpha = (1 + 1/(2*johnson_multiplicity)) * sqrt(1/rate_inverse)
    agreement_cap = floor(alpha * johnson_fiber_count)
  With multiplicity 10 the slack is 1 + 1/20 = 21/20, which is exactly the
  literal the Lean uses.

USAGE
    python3 tools/check_param_binding.py

  Exits 0 iff every consumer agrees with the manifest on every bound
  parameter; prints a PASS/FAIL line per check and a PASS/FAIL banner per
  consumer; exits 1 on any mismatch.  A mismatch is a real finding: it means
  the deployed constant and the proven/second-opinion constant have diverged.
  Do NOT "fix" a mismatch by editing the manifest -- investigate the consumer.
"""

from __future__ import annotations

import json
import math
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST_PATH = os.path.join(REPO_ROOT, "manifests", "soundness-params.json")

RUST_LEDGER = os.path.join(
    REPO_ROOT, "crates", "aspis-prover", "examples", "spend_soundness_epro_ledger.rs"
)
RUST_DESCRIPTOR = os.path.join(
    REPO_ROOT, "crates", "aspis-prover", "src", "state_only_good_spend.rs"
)
PY_CHECKER = os.path.join(REPO_ROOT, "tools", "verify_soundness_params.py")
LEAN_PARAMS = os.path.join(
    REPO_ROOT, "AspisFormal", "AspisFormal", "SoundnessParams.lean"
)


# --------------------------------------------------------------------------
# Tiny result recorder.  Each check is scoped to a consumer; the process exits
# nonzero if any check in any consumer failed.
# --------------------------------------------------------------------------
class Report:
    def __init__(self) -> None:
        self._checks: list[tuple[str, str, bool, str]] = []

    def check(self, consumer: str, name: str, ok: bool, detail: str = "") -> None:
        self._checks.append((consumer, name, bool(ok), detail))

    def eq(self, consumer: str, name: str, got, want) -> None:
        ok = got == want
        detail = f"got {got!r}, manifest {want!r}"
        self.check(consumer, name, ok, detail)

    def render(self) -> bool:
        consumers: list[str] = []
        for consumer, *_ in self._checks:
            if consumer not in consumers:
                consumers.append(consumer)
        all_ok = True
        for consumer in consumers:
            rows = [c for c in self._checks if c[0] == consumer]
            consumer_ok = all(row[2] for row in rows)
            all_ok = all_ok and consumer_ok
            banner = "PASS" if consumer_ok else "FAIL"
            print(f"=== {consumer}: {banner} ===")
            for _, name, ok, detail in rows:
                tag = "PASS" if ok else "FAIL"
                line = f"  [{tag}] {name}"
                if detail:
                    line += f"  ({detail})"
                print(line)
            print()
        return all_ok


def read(path: str) -> str:
    if not os.path.isfile(path):
        raise SystemExit(f"FATAL: expected consumer source not found: {path}")
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read()


def squash(text: str) -> str:
    """Collapse all whitespace so formula matches are layout-insensitive."""
    return re.sub(r"\s+", "", text)


def rust_int(text: str) -> int:
    """Parse a Rust integer literal, dropping `_` separators and type suffix."""
    cleaned = text.replace("_", "")
    m = re.match(r"^(\d+)", cleaned)
    if not m:
        raise ValueError(f"not a Rust int literal: {text!r}")
    return int(m.group(1))


# --------------------------------------------------------------------------
# Derivation, computed from the manifest primitives only.
# --------------------------------------------------------------------------
def derive_cap(rate_inverse: int, fiber_count: int, multiplicity: int) -> int:
    alpha = (1.0 + 1.0 / (2.0 * multiplicity)) * math.sqrt(1.0 / rate_inverse)
    return math.floor(alpha * fiber_count)


# --------------------------------------------------------------------------
# Consumer (a): Rust release ledger + Good_spend descriptor.
# --------------------------------------------------------------------------
def check_rust(rep: Report, m: dict) -> None:
    C = "RUST verifier ledger (spend_soundness_epro_ledger.rs)"
    src = read(RUST_LEDGER)

    # const JOHNSON_MULTIPLICITY: f64 = 10.0;
    mm = re.search(
        r"const\s+JOHNSON_MULTIPLICITY\s*:\s*f64\s*=\s*([0-9._]+)\s*;", src
    )
    if mm:
        rep.eq(C, "JOHNSON_MULTIPLICITY literal", int(float(mm.group(1))),
               m["johnson_multiplicity"])
    else:
        rep.check(C, "JOHNSON_MULTIPLICITY literal", False, "declaration not found")

    # let rho: f64 = 1.0 / 512.0;
    rm = re.search(r"let\s+rho\s*:\s*f64\s*=\s*1\.0\s*/\s*([0-9._]+)\s*;", src)
    if rm:
        rep.eq(C, "rho = 1.0 / rate_inverse", int(float(rm.group(1))),
               m["rate_inverse"])
    else:
        rep.check(C, "rho = 1.0 / rate_inverse", False, "rho binding not found")

    # agreement_fraction = (1.0 + 1.0/(2.0*JOHNSON_MULTIPLICITY)) * rho.sqrt()
    want_formula = "(1.0+1.0/(2.0*JOHNSON_MULTIPLICITY))*rho.sqrt()"
    has_formula = want_formula in squash(src)
    rep.check(C, "agreement_fraction slack formula (1+1/(2m))*sqrt(rho)",
              has_formula, "" if has_formula else "expected formula substring absent")

    # let query_fibers = 131_072u64;
    qm = re.search(r"let\s+query_fibers\s*=\s*([0-9_]+)u64\s*;", src)
    if qm:
        rep.eq(C, "query_fibers literal", rust_int(qm.group(1)),
               m["johnson_fiber_count"])
    else:
        rep.check(C, "query_fibers literal", False, "query_fibers binding not found")

    # assert_eq!(agreement_fibers, 6_082);
    am = re.search(r"assert_eq!\s*\(\s*agreement_fibers\s*,\s*([0-9_]+)\s*\)", src)
    if am:
        rep.eq(C, "pinned agreement cap assertion", rust_int(am.group(1)),
               m["agreement_cap"])
    else:
        rep.check(C, "pinned agreement cap assertion", False,
                  "agreement_fibers assert not found")

    # ---- descriptor string in state_only_good_spend.rs ----
    D = "RUST Good_spend descriptor (state_only_good_spend.rs)"
    dsrc = read(RUST_DESCRIPTOR)
    dm = re.search(
        r'SPEND_GOOD_SCHEDULE_DESCRIPTOR\s*:\s*&\[u8\]\s*=\s*b"([^"]*)"', dsrc
    )
    if not dm:
        rep.check(D, "descriptor string present", False,
                  "SPEND_GOOD_SCHEDULE_DESCRIPTOR not found")
        return
    descriptor = dm.group(1)
    fields = dict(
        part.split("=", 1)
        for part in descriptor.split(";")
        if "=" in part
    )

    # rate=1/512
    rate = fields.get("rate", "")
    rate_m = re.match(r"1/(\d+)$", rate)
    if rate_m:
        rep.eq(D, "descriptor rate=1/rate_inverse", int(rate_m.group(1)),
               m["rate_inverse"])
    else:
        rep.check(D, "descriptor rate=1/rate_inverse", False,
                  f"rate field = {rate!r}")

    # query_fibers=131072
    if "query_fibers" in fields:
        rep.eq(D, "descriptor query_fibers", int(fields["query_fibers"]),
               m["johnson_fiber_count"])
    else:
        rep.check(D, "descriptor query_fibers", False, "field absent")

    # q=18
    if "q" in fields:
        rep.eq(D, "descriptor q (queries per branch)", int(fields["q"]),
               m["queries_per_branch"])
    else:
        rep.check(D, "descriptor q", False, "field absent")

    # domain_log=19
    if "domain_log" in fields:
        rep.eq(D, "descriptor domain_log", int(fields["domain_log"]),
               m["codeword_domain_log2"])
    else:
        rep.check(D, "descriptor domain_log", False, "field absent")


# --------------------------------------------------------------------------
# Consumer (b): Python second-opinion checker.
# --------------------------------------------------------------------------
def check_python(rep: Report, m: dict) -> None:
    C = "PYTHON checker (tools/verify_soundness_params.py)"
    src = read(PY_CHECKER)

    # INVERSE_RATE = 512  and  RHO = 1.0 / 512.0
    im = re.search(r"INVERSE_RATE\s*=\s*(\d+)", src)
    if im:
        rep.eq(C, "INVERSE_RATE = rate_inverse", int(im.group(1)),
               m["rate_inverse"])
    else:
        rep.check(C, "INVERSE_RATE", False, "not found")

    rm = re.search(r"RHO\s*=\s*1\.0\s*/\s*([0-9.]+)", src)
    if rm:
        rep.eq(C, "RHO = 1.0 / rate_inverse", int(float(rm.group(1))),
               m["rate_inverse"])
    else:
        rep.check(C, "RHO = 1.0 / rate_inverse", False, "not found")

    # LOG_DOMAIN = 19  (codeword domain log2)
    lm = re.search(r"LOG_DOMAIN\s*=\s*(\d+)", src)
    if lm:
        rep.eq(C, "LOG_DOMAIN = codeword_domain_log2", int(lm.group(1)),
               m["codeword_domain_log2"])
    else:
        rep.check(C, "LOG_DOMAIN", False, "not found")

    # N = 131072  (QUERY_FIBERS = 1 << (LOG_DOMAIN - 2); the check line pins the
    # literal 131072 explicitly).
    has_fiber = str(m["johnson_fiber_count"]) in src
    rep.check(C, "fiber count literal present (131072)", has_fiber,
              "" if has_fiber else "literal absent")

    # QUERY_COUNT = 18
    qm = re.search(r"QUERY_COUNT\s*=\s*(\d+)", src)
    if qm:
        rep.eq(C, "QUERY_COUNT = queries_per_branch", int(qm.group(1)),
               m["queries_per_branch"])
    else:
        rep.check(C, "QUERY_COUNT", False, "not found")

    # JOHNSON_MULTIPLICITY = 10.0
    jm = re.search(r"JOHNSON_MULTIPLICITY\s*=\s*([0-9.]+)", src)
    if jm:
        rep.eq(C, "JOHNSON_MULTIPLICITY = manifest multiplicity",
               int(float(jm.group(1))), m["johnson_multiplicity"])
    else:
        rep.check(C, "JOHNSON_MULTIPLICITY", False, "not found")

    # johnson_alpha slack: (1.0 + 1.0/(2.0*JOHNSON_MULTIPLICITY)) * math.sqrt(RHO)
    want_formula = "(1.0+1.0/(2.0*JOHNSON_MULTIPLICITY))*math.sqrt(RHO)"
    has_formula = want_formula in squash(src)
    rep.check(C, "alpha slack formula (1+1/(2m))*sqrt(rho)", has_formula,
              "" if has_formula else "expected formula substring absent")

    # cap 6082 pinned via check("... = 6082", A, 6082, exact=True)
    cap_m = re.search(r"floor\(alpha\s*N\)\s*=\s*(\d+)", src)
    if cap_m:
        rep.eq(C, "agreement cap literal in check name", int(cap_m.group(1)),
               m["agreement_cap"])
    else:
        # Fall back to the explicit target argument.
        alt = re.search(r"agreement cap.*?,\s*A\s*,\s*(\d+)", src)
        if alt:
            rep.eq(C, "agreement cap target", int(alt.group(1)),
                   m["agreement_cap"])
        else:
            rep.check(C, "agreement cap literal", False, "6082 check not found")


# --------------------------------------------------------------------------
# Consumer (c): Lean formalization.
# --------------------------------------------------------------------------
def check_lean(rep: Report, m: dict) -> None:
    C = "LEAN formalization (AspisFormal/SoundnessParams.lean)"
    src = read(LEAN_PARAMS)
    sq = squash(src)

    # rho := 1 / 512
    rm = re.search(r"def\s+rho\s*:\s*\S+\s*:=\s*1\s*/\s*(\d+)", src)
    if rm:
        rep.eq(C, "rho := 1 / rate_inverse", int(rm.group(1)), m["rate_inverse"])
    else:
        rep.check(C, "rho := 1 / rate_inverse", False, "rho def not found")

    # Nfib := 131072
    nm = re.search(r"def\s+Nfib\s*:\s*\S+\s*:=\s*(\d+)", src)
    if nm:
        rep.eq(C, "Nfib := johnson_fiber_count", int(nm.group(1)),
               m["johnson_fiber_count"])
    else:
        rep.check(C, "Nfib := fiber_count", False, "Nfib def not found")

    # alpha := (21 / 20) * Real.sqrt rho  -- parse the slack numerator/denominator
    am = re.search(
        r"def\s+alpha\s*:\s*\S+\s*:=\s*\(\s*(\d+)\s*/\s*(\d+)\s*\)\s*\*\s*Real\.sqrt\s+rho",
        src,
    )
    if am:
        num, den = int(am.group(1)), int(am.group(2))
        rep.check(C, "alpha slack literal is (21/20)",
                  (num, den) == (21, 20), f"got ({num}/{den})")
        # 21/20 must equal 1 + 1/(2*multiplicity) from the manifest.
        expected_slack = 1.0 + 1.0 / (2.0 * m["johnson_multiplicity"])
        got_slack = num / den
        rep.check(
            C, "alpha slack (21/20) == 1 + 1/(2*manifest_multiplicity)",
            abs(got_slack - expected_slack) < 1e-12,
            f"lean {num}/{den}={got_slack}, manifest 1+1/(2*{m['johnson_multiplicity']})={expected_slack}",
        )
    else:
        rep.check(C, "alpha slack literal", False, "alpha def not matched")

    # johnson_cap theorem pins 6082 <= alpha*Nfib < 6083
    lo = re.search(r"\(\s*(\d+)\s*:[^)]*\)\s*(?:≤|<=)\s*alpha\s*\*\s*Nfib", src)
    hi = re.search(r"alpha\s*\*\s*Nfib\s*<\s*(\d+)", src)
    if lo:
        rep.eq(C, "cap lower bound literal = agreement_cap",
               int(lo.group(1)), m["agreement_cap"])
    else:
        rep.check(C, "cap lower bound literal", False, "6082 bound not found")
    if hi:
        rep.eq(C, "cap upper bound literal = agreement_cap + 1",
               int(hi.group(1)), m["agreement_cap"] + 1)
    else:
        rep.check(C, "cap upper bound literal", False, "6083 bound not found")


def check_manifest_self_derivation(rep: Report, m: dict) -> None:
    C = "MANIFEST self-derivation (single source of truth)"
    derived = derive_cap(
        m["rate_inverse"], m["johnson_fiber_count"], m["johnson_multiplicity"]
    )
    rep.eq(C, "floor(alpha * N) re-derived from manifest primitives == agreement_cap",
           derived, m["agreement_cap"])


def main() -> int:
    with open(MANIFEST_PATH, "r", encoding="utf-8") as handle:
        m = json.load(handle)

    print("=" * 74)
    print("Aspis soundness parameter binding guard")
    print(f"manifest: {MANIFEST_PATH}")
    print("one source of truth -> Rust verifier, Python checker, Lean proof")
    print("=" * 74)
    print()
    print("Manifest values:")
    for key in (
        "rate_inverse", "codeword_domain_log2", "johnson_fiber_count",
        "queries_per_branch", "johnson_multiplicity", "agreement_cap",
    ):
        print(f"  {key} = {m[key]}")
    print()

    rep = Report()
    check_manifest_self_derivation(rep, m)
    check_rust(rep, m)
    check_python(rep, m)
    check_lean(rep, m)

    all_ok = rep.render()

    print("-" * 74)
    if all_ok:
        print("RESULT: PASS -- every consumer binds to the manifest on every "
              "parameter.")
        print("        The Lean proof, Python checker, and Rust verifier all "
              "speak about the")
        print("        SAME deployed constants; the reviewer's "
              "'intended vs deployed' gap is closed.")
        return 0
    print("RESULT: FAIL -- a consumer disagrees with the manifest.")
    print("        This is a real finding. Investigate the consumer; do NOT "
          "edit the manifest to hide it.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
