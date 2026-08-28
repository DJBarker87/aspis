#!/usr/bin/env python3
"""Create the extraction-only validation view of gamma-combine.

The selected source hash is checked before editing.  The transform preserves
the exact length guards and both canonical decoders, and erases only the
infallible field arithmetic that follows successful decoding.  It must never
be applied to a production or release worktree.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys

SELECTED_SHA256 = "cd652c0fafb7d9a1e0f218e249fa1eea2b4bf6e8f3690053741dd1b005d4c0a8"
START = "    let c1 = decode_packed_m31_eight_aligned::<V6_C1_LIMBS_PER_QUERY>(c1_packed)?;\n"
END = "    Ok(combined)\n}"
GAMMA_SIGNATURE = """pub fn gamma_combine_v6_packed_layer0(
    c1_packed: &[u8],
    c2_packed: &[u8],
    powers: &StateOnlySpendQueryPowers,
)"""
NORMALIZED_GAMMA_SIGNATURE = GAMMA_SIGNATURE.replace("    powers:", "    _powers:")
REPLACEMENT = """    let _c1 = decode_packed_m31_eight_aligned::<V6_C1_LIMBS_PER_QUERY>(c1_packed)?;
    let _c2 = decode_packed_m31_eight_aligned::<V6_C2_LIMBS_PER_QUERY>(c2_packed)?;
    Ok([QM31::ZERO; 4])
}"""


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: normalize_gamma_validation.py INPUT OUTPUT")
    source_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])
    raw = source_path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != SELECTED_SHA256:
        raise SystemExit(f"unexpected selected source hash: {digest}")
    source = raw.decode("utf-8")
    start = source.find(START)
    if start < 0 or source.find(START, start + 1) >= 0:
        raise SystemExit("expected unique gamma arithmetic start marker")
    end_marker = source.find(END, start)
    if end_marker < 0:
        raise SystemExit("gamma arithmetic end marker missing")
    end = end_marker + len(END)
    normalized = source[:start] + REPLACEMENT + source[end:]
    if normalized.count(GAMMA_SIGNATURE) != 1:
        raise SystemExit("expected unique gamma signature")
    normalized = normalized.replace(GAMMA_SIGNATURE, NORMALIZED_GAMMA_SIGNATURE)
    output_path.write_text(normalized, encoding="utf-8")


if __name__ == "__main__":
    main()
