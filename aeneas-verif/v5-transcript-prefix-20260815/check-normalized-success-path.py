#!/usr/bin/env python3
"""Check the typed prefix normalization against the pinned Aeneas function.

This is intentionally a narrow, commit-specific checker rather than a Lean
parser.  It removes whitespace, verifies every retained source expression in
order, checks that no transcript-affecting external call was omitted, and
checks the corresponding typed Lean expression in order.  Any generated-code
change requires an explicit update to this mapping.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path


PINNED_FUNS_SHA256 = (
    "19564142fdddd93b41674554d42df8a0486763b5ce765682b83103408b13b063"
)


def compact(value: str) -> str:
    return re.sub(r"\s+", "", value)


def ordered_find(haystack: str, needles: list[str], label: str) -> None:
    cursor = 0
    for number, raw_needle in enumerate(needles, start=1):
        needle = compact(raw_needle)
        position = haystack.find(needle, cursor)
        if position < 0:
            raise ValueError(f"missing or out-of-order {label} item {number}: {raw_needle}")
        cursor = position + len(needle)


SOURCE_CALLS = [
    """
    let i1 ← aspis_core.transcript.label.PROFILE
    let transcript1 ← aspis_core.transcript.Transcript.absorb transcript i1
      v5_cu_probe.V5_REAL_HOST_TRANSCRIPT_DOMAIN
    """,
    """
    let a ← aspis_core.proof.M31_CIRCLE_BASIS_DISCRIMINATOR
    let s1 ← lift (Array.to_slice a)
    let i2 ← aspis_core.transcript.label.M31_CIRCLE_BASIS
    let transcript2 ←
      aspis_core.transcript.Transcript.absorb transcript1 i2 s1
    """,
    """
    let s2 ← lift (Array.to_slice statement_digest)
    let i3 ← aspis_core.transcript.label.STATEMENT
    let transcript3 ←
      aspis_core.transcript.Transcript.absorb transcript2 i3 s2
    """,
    """
    let a1 ← v5_cu_probe.v5_public_fs_salt parsed.v5_wire_prefix 0#usize
    let transcript4 ←
      v5_cu_probe.absorb_real_v5_round_root transcript3 0#usize
        parsed.v5_private_roots.c1 a1
    """,
    """
    let (r1, transcript5) ←
      aspis_core.transcript.Transcript.challenge_qm31 transcript4
    """,
    """
    let (r3, transcript6) ←
      aspis_core.transcript.Transcript.challenge_qm31 transcript5
    """,
    """
    let a2 ← v5_cu_probe.v5_public_fs_salt parsed.v5_wire_prefix 1#usize
    let transcript7 ←
      v5_cu_probe.absorb_real_v5_c2_root transcript6
        parsed.v5_private_roots.c2 a2
    """,
    """
    let (r5, transcript8) ←
      aspis_core.state_only_sumcheck.begin_state_only_zerocheck transcript7
    """,
    """
    let i4 ← v5_cu_probe.V5_CU_REAL_PREFIX_INITIAL_B_CLAIM_OFFSET
    let r7 ← v5_cu_probe.decode_prefix_qm31 parsed.v5_wire_prefix i4
    """,
    """
    let (r8, transcript9) ←
      aspis_core.state_only_hiding.begin_state_only_masked_sumcheck
        transcript8 val3
    """,
    """
    let i5 ← v5_cu_probe.V5_CU_REAL_PREFIX_SUMCHECK_OFFSET
    let i6 ← v5_cu_probe.V5_CU_REAL_PREFIX_CLAIMS_OFFSET
    let s3 ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      parsed.v5_wire_prefix { start := i5, «end» := i6 }
    let (r10, transcript10) ←
      aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming
        transcript9 s3 val3
    """,
    """
    let i7 ← v5_cu_probe.V5_CU_REAL_PREFIX_TERMINAL_OFFSET
    """,
    """
    let i8 ← aspis_core.transcript.label.M31_CIRCLE_STATEMENT_POINTS
    let transcript11 ←
      aspis_core.transcript.Transcript.absorb transcript10
        i8 parsed.relation_points
    """,
    """
    let i9 ← aspis_core.transcript.label.M31_CIRCLE_STATEMENT_EVALUATIONS
    let transcript12 ←
      aspis_core.transcript.Transcript.absorb transcript11
        i9 parsed.relation_claims
    """,
    """
    let i13 ← v5_cu_probe.V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET
    let s5 ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) parsed.v5_wire_prefix
      { start := i7, «end» := i13 }
    let i14 ← aspis_core.transcript.label.CLAIM
    let transcript13 ←
      aspis_core.transcript.Transcript.absorb transcript12 i14 s5
    """,
    """
    let (r15, transcript14) ←
      v5_cu_probe.check_and_absorb_real_v5_batch_nonce
        transcript13 parsed.v5_batch_nonce
    """,
    """
    let (r16, transcript15) ←
      aspis_core.transcript.Transcript.challenge_nonzero_qm31 transcript14
    """,
    """
    let r18 ← v5_cu_probe.decode_prefix_qm31
      parsed.v5_wire_prefix i13
    """,
    """
    let i15 ← v5_cu_probe.V5_CU_REAL_PREFIX_RESERVED_OFFSET
    let s6 ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) parsed.v5_wire_prefix
      { start := i13, «end» := i15 }
    let i16 ← aspis_core.transcript.label.SECOND_PHASE_CLAIM
    let transcript16 ←
      aspis_core.transcript.Transcript.absorb transcript15 i16 s6
    """,
    """
    let (r19, transcript17) ←
      aspis_core.transcript.Transcript.challenge_nonzero_qm31 transcript16
    """,
]


NORMALIZED_CALLS = [
    ".absorb .profile (AbsorbSlot.label .profile) profileDomain",
    ".absorb .basis (AbsorbSlot.label .basis) circleBasisIdentifier",
    ".absorb .statement (AbsorbSlot.label .statement) (bytes input.statementDigest)",
    ".absorbRoundRoot 0 (bytes (input.circleRoot 0)) (bytes (input.publicSalt 0))",
    ".challengeQm31 .lambda derived.lambda",
    ".challengeQm31 .chi derived.chi",
    ".absorbC2Root (bytes input.c2Root) (bytes (input.publicSalt 1))",
    ".beginZerocheck derived.theta derived.zerocheckPoint derived.mu",
    ".beginMaskedSumcheck values.initialClaim derived.eta",
    """
    .verifySemanticSumcheck (semanticSumcheckWire input) values.initialClaim
      derived.relationChallenge values.terminalClaim
    """,
    ".absorb .relationPoints (AbsorbSlot.label .relationPoints) (bytes input.relationPoints)",
    """
    .absorb .statementEvaluations (AbsorbSlot.label .statementEvaluations)
      (bytes input.statementEvaluations)
    """,
    ".absorb .terminalClaims (AbsorbSlot.label .terminalClaims) (bytes input.terminalClaims)",
    ".checkAndAbsorbBatchNonce input.batchNonce",
    ".challengeNonzeroQm31 .gamma derived.gamma",
    ".absorb .inactiveClaim (AbsorbSlot.label .inactiveClaim) (bytes input.inactiveClaim)",
    ".challengeNonzeroQm31 .kappa derived.kappa",
]


SOURCE_DATAFLOW = [
    """
    lambda := val, chi := val1, theta := val2.theta,
    zerocheck_point := val2.zerocheck_point, mu := val2.mu, eta := val4
    """,
    """
    eta := val4, round_challenges := val5.point, gamma := val9,
    kappa := val11, terminal_real := val6, terminal_mask := val7,
    terminal_masked := val8, inactive_claim := val10
    """,
]


NORMALIZED_DATAFLOW = [
    """
    lambda := derived.lambda
    chi := derived.chi
    theta := derived.theta
    zerocheckPoint := derived.zerocheckPoint
    mu := derived.mu
    eta := derived.eta
    """,
    """
    eta := derived.eta
    roundChallenges := derived.relationChallenge
    gamma := derived.gamma
    kappa := derived.kappa
    terminalReal := values.terminalReal
    terminalMask := values.terminalMask
    terminalMasked := values.terminalMasked
    inactiveClaim := values.inactiveClaim
    """,
]


EXTERNAL_CALL_COUNTS = {
    "aspis_core.transcript.Transcript.absorb": 7,
    "aspis_core.transcript.Transcript.challenge_qm31": 2,
    "aspis_core.transcript.Transcript.challenge_nonzero_qm31": 2,
    "v5_cu_probe.absorb_real_v5_round_root": 1,
    "v5_cu_probe.absorb_real_v5_c2_root": 1,
    "aspis_core.state_only_sumcheck.begin_state_only_zerocheck": 1,
    "aspis_core.state_only_hiding.begin_state_only_masked_sumcheck": 1,
    "aspis_core.state_only_sumcheck.verify_state_only_sumcheck_streaming": 1,
    "v5_cu_probe.check_and_absorb_real_v5_batch_nonce": 1,
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("generated_funs", type=Path)
    parser.add_argument("normalized_lean", type=Path)
    args = parser.parse_args()

    generated_bytes = args.generated_funs.read_bytes()
    digest = hashlib.sha256(generated_bytes).hexdigest()
    if digest != PINNED_FUNS_SHA256:
        raise ValueError(f"unexpected generated Funs.lean SHA-256: {digest}")

    generated = generated_bytes.decode("utf-8")
    start_marker = "def v5_cu_probe.verify_v5_wire_prefix_from_initialized_transcript"
    start = generated.index(start_marker)
    end = generated.index("\nend V5TranscriptPrefixCoreGenerated", start)
    function = compact(generated[start:end])
    normalized = compact(args.normalized_lean.read_text(encoding="utf-8"))

    ordered_find(function, SOURCE_CALLS, "generated-call")
    ordered_find(normalized, NORMALIZED_CALLS, "normalized-call")
    ordered_find(function, SOURCE_DATAFLOW, "generated-dataflow")
    ordered_find(normalized, NORMALIZED_DATAFLOW, "normalized-dataflow")

    for name, expected in EXTERNAL_CALL_COUNTS.items():
        actual = function.count(name)
        if actual != expected:
            raise ValueError(
                f"unexpected count for {name}: expected {expected}, found {actual}"
            )

    constructor_count = sum(normalized.count(compact(item)) for item in NORMALIZED_CALLS)
    if constructor_count != 17:
        raise ValueError(
            f"expected 17 normalized transcript calls, found {constructor_count}"
        )

    print("checked normalized V5 prefix calls, arguments, context, and return flow")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, UnicodeError, ValueError) as error:
        print(f"normalization check failed: {error}", file=sys.stderr)
        sys.exit(1)
