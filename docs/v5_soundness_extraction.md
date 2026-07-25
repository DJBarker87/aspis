# V5 (tag-67) Soundness Extraction

**Purpose.** Everything a cryptographer needs to build a *fresh* finite-event soundness
certificate for the deployed V5 verifier, without reading the repository. No probability, bit
count, or security level appears anywhere in this document.

**Scope.** Only code compiled by `--features v5-production-tag67` and reachable from the tag-67
dispatcher. Entry point, `programs/aspis-verifier/src/dispatch.rs:208-214`:

```rust
        #[cfg(feature = "v5-production-tag67")]
        67 => crate::v5_full_transaction::process_v5_full_cu_transaction_with_verifier(
            program_id,
            accounts,
            instruction_data,
            crate::v5_cu_probe::verify_uploaded_v5_mode9_cu_fixture,
        ),
```

Released SBF built `--no-default-features --features v5-production-tag67`
(`release/aspis-v5-tag67-frozen-candidate-v1/provenance/build-provenance.json:472-482`).
Excluded and not analysed: `v5-cu-probe` entrypoint (gated
`v5_cu_probe.rs:124-129`), tag 66, all `#[cfg(not(target_os = "solana"))]` items, all
`#[cfg(test)]` items. Where such a path is adjacent to a production path it is named and marked
EXCLUDED.

**Standing assumption of this document:** nothing from the q18/Profile-23 certificate is assumed
to transfer. Part 10 states the mapping that was proved, and only that.

Paths are relative to the repository root; `v5_cu_probe.rs`, `v5_fri_checks.rs`,
`v5_private_openings.rs`, `v5_atomic_terminal.rs`, `v5_relation_stress.rs`,
`v5_good_gate_probe.rs`, `v5_wire_skeleton.rs`, `v5_full_transaction.rs`, `dispatch.rs` all live
in `programs/aspis-verifier/src/`. `transcript.rs`, `state_only_sumcheck.rs`,
`state_only_hiding.rs`, `state_only_prefix.rs`, `sumcheck.rs`, `circle_hiding_prefix.rs`,
`state_only_private_merkle.rs` live in `crates/aspis-core/src/`.

---

## Part 1 — The exact interactive protocol

### 1.0 Objects on the wire

Single account body, magic `AV5CUP08` (`v5_cu_probe.rs:234`), fixed public region of
19,136 bytes (`v5_cu_probe.rs:4628`: `assert_eq!(V5_CU_PROBE_ACCOUNT_BYTES, 19_136)`) followed by
five variable-length private-opening sections. Parsed by `parse_probe_data`
(`v5_cu_probe.rs:531-540`) into the fields listed at `v5_cu_probe.rs:496-527`.

Two commitments plus three later-layer commitments — five Merkle roots total
(`v5_private_openings.rs:21-32`):

```rust
pub const V5_PRIVATE_LAYER0_LEAVES: usize = 1 << 17;
pub const V5_PRIVATE_SECTION_COUNT: usize = 5;
pub const V5_PRIVATE_DEPTHS: [u32; V5_PRIVATE_SECTION_COUNT] = [17, 17, 15, 13, 11];
pub const V5_PRIVATE_VALUE_WIDTHS: [usize; V5_PRIVATE_SECTION_COUNT] = [256, 192, 64, 64, 64];
pub const V5_PRIVATE_TREE_TAGS: [u8; V5_PRIVATE_SECTION_COUNT] = [
    CIRCLE_C1_LAYER0_TAG,
    CIRCLE_C2_LAYER0_TAG,
    CIRCLE_LINE_TAGS[0],
    CIRCLE_LINE_TAGS[1],
    CIRCLE_LINE_TAGS[2],
];
```

PCS shape (`v5_fri_checks.rs:45-56`):

```rust
pub const V5_FRI_PCS_SHAPE: CirclePcsShape = CirclePcsShape {
    trace_log_size: 10,
    domain_log_size: 19,
    query_count: STATE_ONLY_SPEND_QUERY_COUNT,
    opening_points: V5_FRI_OPENING_POINTS as u8,
    c1_columns: 16,
    c2_columns: 3,
    c1_layer0_tag: CIRCLE_C1_LAYER0_TAG,
    c2_layer0_tag: CIRCLE_C2_LAYER0_TAG,
    later_layer_tags: CIRCLE_LINE_TAGS,
};
```

Merkle topology `Radix4BinaryCapTopology` (`v5_private_openings.rs:15`); every leaf carries a
32-byte private salt appended to its value region (`v5_cu_probe.rs:141-148`;
`STATE_ONLY_PRIVATE_LEAF_SALT_BYTES = 32` at `state_only_private_merkle.rs:11`).

### 1.1 Pre-transcript structural gate

Order is exactly as executed in `verify_uploaded_v5_mode9_cu_fixture`
(`v5_cu_probe.rs:2446-2466`) → `verify_mode9_composite_with_live_statement`
(`v5_cu_probe.rs:2384-2423`) → `verify_v5_wire_prefix` (`v5_cu_probe.rs:1399-1516`).

1. `proof_account_finalized(data)` — `v5_cu_probe.rs:2429`.
2. Declared body exhausts the account: `proof_end != data.len()` rejects —
   `v5_cu_probe.rs:2432-2436`.
3. `data.len() <= V5_CU_PROBE_MAX_PROOF_BODY_BYTES` — `v5_cu_probe.rs:534-536`.
4. `v5_work_wire_magic_is_valid(data)` — `v5_cu_probe.rs:483`.
5. γ decodes canonically from the account — `v5_cu_probe.rs:494-496`.
6. `v5_wire_prefix_header_is_valid(prefix)` — `v5_cu_probe.rs:1406-1408`.
7. 400-byte reserved prefix tail all-zero — `verify_v5_reserved_tail`, `v5_cu_probe.rs:1413`.
8. Prefix-carried roots equal the five private-opening roots —
   `v5_prefix_roots_match_private`, `v5_cu_probe.rs:1415-1417`.
9. Live statement digest recomputed from the wrapper's statement and matched —
   `verify_live_statement_digest`, `v5_cu_probe.rs:1421`.

### 1.2 Prefix phase — messages, challenges, checks

Verbatim head, `v5_cu_probe.rs:1423-1437`:

```rust
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label::PROFILE, V5_REAL_HOST_TRANSCRIPT_DOMAIN);
    transcript.absorb(label::M31_CIRCLE_BASIS, M31_CIRCLE_BASIS_DISCRIMINATOR);
    transcript.absorb(label::STATEMENT, statement_digest);
    absorb_real_v5_round_root(&mut transcript, 0, c1_root, v5_public_fs_salt(prefix, 0));
    let lambda = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let chi = transcript
        .challenge_qm31()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    absorb_real_v5_c2_root(&mut transcript, c2_root, v5_public_fs_salt(prefix, 1));
```

Then `begin_state_only_zerocheck` (theta, ten zerocheck coordinates, mu),
`begin_state_only_masked_sumcheck` (eta), the ten-round degree-27 semantic sumcheck,
point/claim absorbs, the terminal triple, batch PoW, γ, the inactive claim, κ. Full step table in
Part 8.

Prefix algebraic checks:

- **Ten-round sumcheck boundary.** Each round: `state_only_boundary_sum(&polynomial) != running_claim`
  rejects — `state_only_sumcheck.rs:272-274`. `STATE_ONLY_SUMCHECK_ROUNDS = 10`,
  `STATE_ONLY_SUMCHECK_DEGREE = 27`, `STATE_ONLY_SUMCHECK_COEFFICIENTS = 28`
  (`state_only_sumcheck.rs:13-15`).
- **Point/claim table binding**, `v5_cu_probe.rs:1449-1455`:

```rust
    let expected_points = encode_relation_points(&semantic.point);
    if parsed.relation_points != expected_points
        || &prefix[V5_CU_REAL_PREFIX_CLAIMS_OFFSET..V5_CU_REAL_PREFIX_TERMINAL_OFFSET]
            != parsed.relation_claims
    {
        return Err(ProgramError::InvalidAccountData);
    }
```

- **Semantic terminal agreement**: `terminal_masked != semantic.terminal_claim` rejects —
  `v5_cu_probe.rs:1466-1468`.
- **Scale table binding**, `v5_cu_probe.rs:1486-1493`:

```rust
    if parsed.gamma != gamma
        || decode_qm31(parsed.relation_scales, 0)? != QM31::ONE
        || decode_qm31(parsed.relation_scales, 1)? != kappa
        || decode_qm31(parsed.relation_scales, 2)? != kappa.square()
    {
        return Err(ProgramError::InvalidAccountData);
    }
```

- **Context equality**: the proof-carried atomic-terminal context must reproduce the live
  statement and the exact challenge tuple — `v5_cu_probe.rs:1495-1508`:

```rust
    let expected_context = V5AtomicTerminalChallenges {
        lambda,
        chi,
        theta: batching.theta,
        zerocheck_point: batching.zerocheck_point,
        mu: batching.mu,
        eta,
    };
    if &context_statement != live_statement || context != expected_context {
        return Err(ProgramError::InvalidAccountData);
    }
```

### 1.3 Semantic terminal (Component B mask, Component C excluded)

`v5_atomic_terminal.rs:1-12` states the V5 change and is load-bearing, so quoted verbatim:

```rust
//! V5-only adapter for the unchanged atomic-v3 semantic terminal.
//!
//! The atomic evaluator's historical input is three rows of 28 claims:
//! sixteen semantic C1 lanes, ten v4 mask-only lanes, Hcopy, and G.  V5 keeps
//! the sixteen semantic lanes and Hcopy, but removes the ten mask-only lanes
//! and G.  This module therefore calls the *unmasked* atomic evaluator after
//! embedding the authenticated v5 point claims into the historical shape.
//! Component B's authenticated fourth opening supplies the new mask term:
//!
//! `terminal_masked = terminal_mask + eta * terminal_real`.
//!
//! Component C is a PCS-view mask and is not a semantic-terminal input.
```

`verify_v5_atomic_terminal_from_bytes` (`v5_atomic_terminal.rs:263-330`) performs, in order:

1. Claim-byte length exactly `V5_ATOMIC_TERMINAL_CLAIM_BYTES = 1216` (`:270-275`, `:35`).
2. Point-byte length exactly `V5_ATOMIC_TERMINAL_POINT_BYTES = 480` and every coordinate
   canonical (`decode_points`, `:222-243`).
3. **Point-structure identities** (`:278-283`):

```rust
    if points[1] != successor_point(&points[0]) {
        return Err(V5AtomicTerminalError::OpeningPointMismatch { point: 1 });
    }
    if points[2] != xor12_point(&points[0]) {
        return Err(V5AtomicTerminalError::OpeningPointMismatch { point: 2 });
    }
```

4. Legacy embedding: 16 semantic lanes into legacy slots 0..16, the Hcopy lane into legacy slot
   26; legacy mask-only slots 16..26 and legacy G slot 27 **left zero** (`:289-300`, with the
   comment at `:285-288` recording that calling the masked wrapper here is "forbidden by
   construction"). Constants `LEGACY_COLUMNS = 28`, `LEGACY_CLAIMS = 84`,
   `LEGACY_MASK_ONLY_START = 16`, `LEGACY_HCOPY_COLUMN = 26`, `LEGACY_G_COLUMN = 27` (`:50-54`).
5. **Real terminal identity**: `atomic_state_only_selected_unmasked_terminal_value_compiled_v3(...)`
   over `(statement, legacy, points[0], lambda, chi, theta, zerocheck_point, mu)`; mismatch with
   `claimed.real` rejects (`:302-314`).
6. **Mask identity**: `mask` is the 4th claim of the Component-B lane; mismatch with
   `claimed.mask` rejects (`:316-323`).
7. **Masked identity** (`:324-327`):

```rust
    let masked = mask.add(challenges.eta.mul(real));
    if masked != claimed.masked {
        return Err(V5AtomicTerminalError::MaskedMismatch);
    }
```

Lane map (`v5_atomic_terminal.rs:25-31`): semantic 0..16, Hcopy 16, Component-B 17,
Component-C 18; `V5_ATOMIC_TERMINAL_LANES = 19`, `CLAIMS_PER_LANE = 4`, `POINT_CLAIMS = 3`.
**Component C is never an input to this identity** (module docstring, `:12`).

### 1.4 Relation-round phase — 4 rounds × 2 OOD samples

Transcript replay, `replay_real_v5_relation_rounds` (`v5_cu_probe.rs:782-864`).
`V5_RELATION_STRESS_ROUNDS = 4`, `V5_RELATION_STRESS_OOD_SAMPLES = 2`
(`v5_relation_stress.rs:16-17`).

Per (round, sample): squeeze the OOD point — round 0 `challenge_secure_circle_point()`
(`:786-788`), rounds 1–3 `challenge_ood_qm31()` (`:800-802`) — check it equals the stress-region
value (`:789-795`, `:803-812`), absorb the OOD value under `M31_CIRCLE_OOD_VALUE` (round 0) or
`M31_LINE_OOD_VALUE` (`:818-828`), squeeze `mix`, check it equals the stress-region value
(`:832-838`).

Per round: absorb the 7-coefficient relation sumcheck (`SUMCHECK_COEFFICIENTS = 7`,
`sumcheck.rs:18`) (`:840-846`), check + absorb the fold PoW (`:848`), squeeze α, check it equals
`relation_alphas[round]` (`:852-854`), then absorb later root `round+1` with public FS salt
`round+2` when `round < later.len()` (`:854-860`).

Independently, `verify_v5_relation_stress_with_additive` (`v5_relation_stress.rs:139-198`)
re-executes the same algebra over the *same* payload and the transcript α's. Its checks:

- **Circle-point on-curve**, `v5_relation_stress.rs:148-155`:

```rust
        if point.x.square().add(point.y.square()) != QM31::ONE {
            return Err(V5RelationStressError::InvalidCirclePoint { sample });
        }
```

- **Claim accumulation**: `running_claim = running_claim.add(mix.mul(value))` per observation,
  with `weights.add_circle_tensor(mix, circle_points[sample])` for round 0 and
  `weights.add_line_tensor(mix, point)` for rounds 1–3 (`:158-171`).
- **Relation sumcheck boundary** per round (`:173-181`):

```rust
        if boundary_sum(&polynomial) != running_claim {
            return Err(V5RelationStressError::BoundaryMismatch { round });
        }
        running_claim = evaluate(&polynomial, alpha);
        weights.fold(alpha);
        additive.fold(alpha);
```

- **Terminal dot identity** (`:186-193`):

```rust
    if weights
        .dot(&final_coefficients)
        .add(additive.dot(&final_coefficients))
        != running_claim
    {
        return Err(V5RelationStressError::TerminalMismatch);
    }
```

The `additive` covector is Component-B's compact degree-27 weights
(`CompactBTerminalWeights::new(round_challenges, dense_scale)`, `v5_cu_probe.rs:2365`), sharing
the same four folds and the same final dot (trait `V5RelationStressAdditive`,
`v5_relation_stress.rs:67-70`).

Declared error variants that are *reachable rejections* and therefore candidate events:
`NonCanonicalField`, `InvalidCirclePoint`, `ZeroMix`, `ZeroAlpha`, `WeightShape`,
`BoundaryMismatch`, `TerminalMismatch` (`v5_relation_stress.rs:44-52`). **`ZeroMix` and
`ZeroAlpha` are declared but are not constructed anywhere in
`verify_v5_relation_stress_with_additive`** — see Part 4 item P4.6 and Part 9 Q-ZERO.

### 1.5 Final binding, selector, queries

`bind_final_and_derive_v5_queries` (`v5_fri_checks.rs:288-326`), verbatim core:

```rust
    transcript.absorb(label::M31_CIRCLE_FINAL_TENSOR_POLY, final_polynomial_bytes);
    if check_pow && !transcript.grinding_ok(final_nonce, STATE_ONLY_SPEND_GRINDING_BITS) {
        return Err(V5QueryBindingError::GrindingRejected);
    }
    transcript.absorb(label::GRIND_NONCE, &final_nonce.to_le_bytes());
    if query_selector >= STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT {
        return Err(V5QueryBindingError::QuerySelectorOutOfRange {
            selector: query_selector,
        });
    }
    transcript.absorb(label::M31_STATE_ONLY_QUERY_CANDIDATE, &[query_selector]);
    let queries = transcript.challenge_queries_without_replacement(
        V5_FRI_QUERY_COUNT,
        V5_PRIVATE_LAYER0_LEAVES as u32,
        PAYMENT_HIDING_QUERY_DRAW_LIMIT,
    )?;
```

`STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT = 3` (`state_only_prefix.rs:165`),
`PAYMENT_HIDING_QUERY_DRAW_LIMIT = 64` (`circle_hiding_prefix.rs:37`),
`V5_FRI_QUERY_COUNT` asserted `== 18` (`v5_fri_checks.rs:58`).

**Good gate.** `candidate_is_good` (`v5_good_gate_probe.rs:1137-1146`):

```rust
pub fn candidate_is_good(
    point: &[QM31; 10],
    queries: [u32; V5_CU_PROBE_QUERY_COUNT],
) -> Option<bool> {
    let kernel = query_kernel(&queries)?;
    let (good_a_matrix, good_b_matrix) = good_matrices(&kernel, point);
    let good_a = m31_matrix_nonsingular(good_a_matrix);
    let good_b = qm31_matrix_nonsingular(good_b_matrix);
    Some(good_a && good_b)
}
```

`GOOD_A_SIZE = 12` over M31, `GOOD_B_SIZE = 4` over QM31
(`v5_good_gate_probe.rs:24-25`). The kernel is
`K(X) = prod_i (X^2 - x_i^2)`, built as a degree-18 polynomial in `Z = X^2` and embedded in the
even coordinates (`v5_good_gate_probe.rs:281-284`, comment quoting the construction; code
`:285-300`). `good_matrices` (`:856-876`) builds the B row 0 from `evaluate_b_inactive` on shifted
directions, then `fill_good_base_and_xor_terminals`, then
`fill_good_successor_terminal` at `binary_successor_point(point)`.

**Only the selected branch is derived and evaluated** (`v5_cu_probe.rs:958-971`):

```rust
fn checked_v5_selected_good_candidate<T: Copy>(
    selected: u8,
    mut derive: impl FnMut(u8) -> Result<T, ProgramError>,
    mut evaluate: impl FnMut(u8, &T) -> Result<bool, ProgramError>,
) -> Result<T, ProgramError> {
    if !v5_query_selector_is_valid(selected) {
        return Err(ProgramError::InvalidAccountData);
    }
    let candidate = derive(selected)?;
    if !evaluate(selected, &candidate)? {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(candidate)
}
```

with the caller's doc comment (`v5_cu_probe.rs:973-976`) ending: *"Honest prover leastness is not
a verifier premise."* `selected_is_least_good` (`v5_good_gate_probe.rs:1150-1155`) exists; its
only non-test caller is `xtask/src/spend_devnet/v5.rs:1885` (host tooling, not the program).
`v5_good_gate_evaluations`, which evaluates all three, is `#[cfg(not(target_os = "solana"))]`
(`v5_cu_probe.rs:1044-1046`) — EXCLUDED from the deployed SBF.

### 1.6 PCS / FRI phase

`verify_v5_private_suffix` (`v5_cu_probe.rs:578`) authenticates the five sections against the five
roots. `check_v5_fri_queries` (`v5_fri_checks.rs:412-555`) then checks:

- Layer-0 opening count equals 18 (`:422-427`); prepared shape (`:431-436`).
- Per query: γ-combine 19 columns (`gamma_combine_v5_layer0_exact`, `:364-409`), fold
  `normalized_circle_to_line_arity4_prepared_polynomial_refs` with `[inv_2x, inv_2y]` (`:480-485`),
  compare to the authenticated parent leaf at `parent = query >> 2`, slot `query & 3`
  (`:488-498`); mismatch → `FirstFoldMismatch`.
- Layers 1→2 and 2→3: `check_fixed_line_transition_prepared_polynomial_powers` (`:526-533`).
- Layer 3→final: `check_fixed_terminal_transition_prepared_polynomial_refs` against the
  4-coefficient final polynomial (`:542-549`).

Leaf widths and canonicity enforced at `:365-388` (C1 256 bytes, C2 192 bytes; `NonCanonicalC1`,
`NonCanonicalC2`).

### 1.7 Final agreement, and the one value that is discarded

`v5_cu_probe.rs:2377-2379`:

```rust
    if relation_stress.final_coefficients != *final_polynomial {
        return Err(ProgramError::InvalidAccountData);
    }
```

`verify_mode9_composite_with_live_statement` returns
`fri_sum.add(relation_claim).add(terminal_masked)` (`v5_cu_probe.rs:2420`); the caller passes it
to `core::hint::black_box` and returns `Ok(())` (`v5_cu_probe.rs:2462-2464`). **No predicate
constrains that sum.** See Part 2 event E-SINK and Part 9 Q-SINK.

---

## Part 2 — Complete event ledger

Each event is framed as instructed: *what false proof passes if this predicate is removed?*
"Algebraic?" = can the acceptance probability be written as a closed-form finite-parameter
expression once the named theorem is granted.

Columns: ID · description · verifier predicate (source) · dependent transcript objects ·
imported theorem required · algebraic?

### Structural / parser events

| ID | If removed, a prover could… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E01** | Submit an unfinalized or over-allocated account so bytes change after commitment | `proof_account_finalized`; `proof_end != data.len()` (`v5_cu_probe.rs:2429-2436`) | account data | Parser/lifecycle correctness | No — combinatorial, not probabilistic |
| **E02** | Enlarge the accepted body beyond the canonical grammar | `data.len() <= V5_CU_PROBE_MAX_PROOF_BODY_BYTES` (`:534-536`) | account length | Parser correctness | No |
| **E03** | Reuse a tag-66 sidecar layout under tag 67 | `v5_work_wire_magic_is_valid` (`:483`) | magic bytes | Parser correctness | No |
| **E04** | Supply non-canonical field elements that alias a different value | canonical decode at `:494-496`, `v5_fri_checks.rs:265-267,377-400`, `v5_relation_stress.rs:88-90` | all field bytes | Canonical-encoding injectivity | No |
| **E05** | Hide material in the 400-byte reserved prefix tail | `verify_v5_reserved_tail` (`:1413`) | prefix tail | Parser correctness | No — see P4.7 |
| **E06** | Commit to one root set and open against another | `v5_prefix_roots_match_private` (`:1415-1417`) | 5 roots, prefix | Merkle binding | No |
| **E07** | Prove against a statement other than the live pool state | `verify_live_statement_digest` (`:1421`); `&context_statement != live_statement` (`:1505-1507`) | statement digest | Hash collision resistance | Yes — collision term |

### Transcript / Fiat–Shamir events

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E08** | Choose challenges after seeing them (all challenges become prover-chosen) | the whole `Transcript` duplex: absorb `:272-274`, squeeze `:283-286` | every absorb/squeeze | Random oracle / BCS state-restoration | Yes, per boundary |
| **E09** | Reuse a root's salt across sections, or fix a salt after seeing a challenge | salt is concatenated into each root record: `real_v5_round_root_absorb_input` → `[u8; 65]` (`:1279-1288`), `real_v5_c2_root_absorb_input` → `[u8; 64]` (`:1291-1298`) | 5 public FS salts | Random oracle; **plus** the prover-side freshness obligation P4.2 | NOT DETERMINABLE — the verifier cannot check freshness |
| **E10** | Substitute a different profile/basis/domain separation | absorbs of `PROFILE`, `M31_CIRCLE_BASIS` (`:1424-1425`) | domain constants | Domain separation / RO | No |

### Semantic-sumcheck events

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E11** | Pass a round polynomial whose boundary sum differs from the running claim (breaks the sumcheck chain at one of ten rounds) | `state_only_boundary_sum(&polynomial) != running_claim` (`state_only_sumcheck.rs:272-274`) | `initial_claim`, `z[0..10]`, 28-coefficient rounds | Sumcheck round-by-round soundness at degree 27 | Yes — per-round, degree 27 |
| **E12** | Decouple the claim table from the sumcheck point | `parsed.relation_points != expected_points \|\| prefix claims != parsed.relation_claims` (`v5_cu_probe.rs:1449-1455`) | `z[0..10]`, claim table | Polynomial-identity / equality of encodings | No |
| **E13** | Assert a terminal claim inconsistent with the sumcheck terminal | `terminal_masked != semantic.terminal_claim` (`:1466-1468`) | sumcheck terminal | — (equality) | No |

### Terminal (Component B / Component C) events

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E14** | Use three unrelated opening points instead of the structured triple | `points[1] != successor_point(points[0])`; `points[2] != xor12_point(points[0])` (`v5_atomic_terminal.rs:278-283`) | 3 × 10 point coordinates | Poseidon2 point-structure lemma (`state_only_poseidon`) | NOT DETERMINABLE — see Part 9 T-PT |
| **E15** | Claim a `real` terminal that the atomic-v3 relation does not evaluate to | `real != claimed.real` (`:312-314`) | 16 semantic + Hcopy claims, `points[0]`, λ, χ, θ, zerocheck point, μ | **Component-B terminal lemma** for the *unmasked* evaluator at 19 lanes | Yes — Schwartz–Zippel on the compiled terminal |
| **E16** | Supply a mask term not equal to Component-B's 4th opening | `mask != claimed.mask` (`:316-323`) | Component-B lane 4th claim | PCS opening soundness | Yes |
| **E17** | Break the masking identity `masked = mask + η·real` | `masked != claimed.masked` (`:324-327`) | η, real, mask | Polynomial-identity lemma in η | Yes — linear in η |
| **E18** | Populate the retired mask-only/G legacy slots to steer the evaluator | slots left zero by construction (`:289-300`); no runtime check | — | **New: legacy-slot-zero lemma** | NOT DETERMINABLE — enforced by code shape, not a predicate |

### Batching event

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E19** | Have one of the 19 committed columns disagree with its claim while the batch still matches | γ-combine and per-query fold comparison (`v5_fri_checks.rs:471-498`); claim dot `:260-274` | γ powers γ⁰…γ¹⁸, 19 columns | **MCA / proximity-gap for a 19-term scalar-powers generator over a mixed M31/QM31 lane set** | Yes — this is the batch term |
| **E20** | Bind a different γ than the transcript's, or a κ-scale table that is not `(1,κ,κ²)` | `v5_cu_probe.rs:1486-1493` | γ, κ | — (equality) | No |

### Relation-stress events

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E21** | Use an OOD circle point off the unit circle | `point.x² + point.y² != 1` (`v5_relation_stress.rs:152-154`) | 2 circle points | Circle-group membership | No |
| **E22** | Use an OOD point inside the evaluation domain | sampler rejects `point.c1 == CM31::ZERO` (`transcript.rs:365-378`); round 0 via `secure_ood_circle_point_from_parameter` (`:382-395`) | OOD points | **OOD-sampling lemma** (domain ⊂ CM31) | Yes — by construction the sampler excludes the domain |
| **E23** | Break the relation sumcheck chain at one of four rounds | `boundary_sum(&polynomial) != running_claim` (`v5_relation_stress.rs:177-179`) | mixes, values, α, 7-coefficient rounds | Sumcheck round-by-round soundness at degree 6 | Yes |
| **E24** | Have the folded weight covector disagree with the final polynomial | `weights.dot(...) + additive.dot(...) != running_claim` (`:186-193`) | α₀..α₃, weights, Component-B covector, 4 final coefficients | **Component-C / dual-fold terminal lemma** + polynomial identity | Yes |
| **E25** | Present stress-region OOD points/values/mixes that differ from the transcript's | equality checks at `v5_cu_probe.rs:789-795, 803-812, 832-838` | all OOD objects | — (equality) | No |
| **E26** | Present fold challenges that differ from the transcript's | `decode_qm31(parsed.relation_alphas, round)? != alpha` (`:852-854`) | α₀..α₃ | — (equality) | No |

### Work events

| ID | If removed… | Predicate (source) | Threshold | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E27** | Retry the batch boundary freely | `require_real_v5_work(..., v5_batch_work_difficulty())` (`:733-737`, `:636-638`) | 37 | Random oracle (grinding) | Yes |
| **E28–E31** | Retry each fold boundary freely | `check_and_absorb_real_v5_fold_nonce` (`:740-750`), `v5_fold_work_difficulty(round)` (`:641-648`) | 34, 33, 30, 25 | Random oracle | Yes |
| **E32** | Retry the final/query boundary freely | `transcript.grinding_ok(final_nonce, STATE_ONLY_SPEND_GRINDING_BITS)` (`v5_fri_checks.rs:305-307`) | 32 | Random oracle | Yes |

Digest input for all six (`transcript.rs:472-475`):

```rust
    pub fn grinding_ok(&self, nonce: u64, bits: u8) -> bool {
        let digest = (self.hash)(&[&self.state, &[DOM_GRIND], &nonce.to_le_bytes()]);
        digest_has_leading_zero_bits(digest, bits)
    }
```

`DOM_GRIND = 0x03` (`transcript.rs:202`). Every check precedes the corresponding absorb.

### Selector and query events

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E33** | Use an out-of-range selector, or more than three schedules | `query_selector >= STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT` (`v5_fri_checks.rs:309-313`); `v5_query_selector_is_valid` (`:963-965`) | selector byte | — (range) | No |
| **E34** | Choose whichever of the three schedules misses the corrupted fibre | selector absorbed **after** the final nonce, before sampling (`v5_fri_checks.rs:314-319`); only the selected branch is evaluated (`v5_cu_probe.rs:958-971`) | selector, query schedule | **New: three-branch selector-scope lemma with no leastness premise** | Yes, but the event is *not* the q18 event — see Part 10 |
| **E35** | Repeat a query index to reduce effective coverage | `challenge_queries_without_replacement` (`transcript.rs:429-462`), draw cap 64 | 18 indices | Without-replacement query-phase bound | Yes |
| **E36** | Present a schedule whose GoodA/GoodB matrices are singular | `candidate_is_good` (`v5_good_gate_probe.rs:1137-1146`) | `z[0..10]`, 18 queries, kernel `K` | **New: GoodA(12×12 over M31)/GoodB(4×4 over QM31) non-singularity lemma** | Yes |

### PCS / FRI events

| ID | If removed… | Predicate (source) | Depends on | Theorem needed | Algebraic? |
|---|---|---|---|---|---|
| **E37** | Open a leaf not committed under the root | `verify_v5_private_suffix` (`:578`) → `verify_state_only_private_opening_from_proof_with_topology` | 5 roots, salts, radix-4 cap topology | **Merkle binding for salted radix-4 leaves with a binary cap** | Yes — collision term |
| **E38** | Open fewer or more than 18 layer-0 fibres | count check (`v5_fri_checks.rs:422-427`) | 18 indices | — | No |
| **E39** | Present a layer-0 word far from the code that still folds correctly at 18 fibres | first-fold comparison (`:488-498`) | γ-combined leaf, α₀, fold inverses | **Johnson/list-decoding + circle→line transport at rate 2^10/2^19** | Yes — dominant query term |
| **E40–E41** | Break a line→line fold at layer 1→2 or 2→3 | `check_fixed_line_transition_prepared_polynomial_powers` (`:526-533`) | α₁, α₂, later leaves | WHIR-style fold-list commutation | Yes |
| **E42** | Break the layer-3 → final-polynomial transition | `check_fixed_terminal_transition_prepared_polynomial_refs` (`:542-549`) | α₃, final coefficients, `final_x` | Fold commutation + terminal identity | Yes |
| **E43** | Present a final polynomial for FRI different from the relation's | `relation_stress.final_coefficients != *final_polynomial` (`v5_cu_probe.rs:2377-2379`) | 4 coefficients | — (equality) | No |

### Non-events (recorded so a certificate does not credit them)

| ID | Observation | Source |
|---|---|---|
| **E-SINK** | `fri_sum + relation_claim + terminal_masked` is computed and discarded via `black_box`. If a cross-identity between the FRI folded sum, the relation terminal, and the masked semantic terminal was intended, it is **not checked**. | `v5_cu_probe.rs:2420`, `:2462-2464` |
| **E-LEAST** | Leastness of the selector is **not** checked on chain. | `v5_cu_probe.rs:958-976` |
| **E-ZERO** | `ZeroMix` / `ZeroAlpha` error variants are declared but never constructed in the production relation path. Mixes and α are drawn with plain `challenge_qm31`, which permits zero. | `v5_relation_stress.rs:47-48` vs `:139-198`; `transcript.rs:307` |

---

## Part 3 — Dependency graph

`T` transcript · `M` Merkle · `B` batching · `K` masking · `RS` relation stress · `CB` Component B ·
`CC` Component C · `TP` terminal polynomial · `FE` final equality · `H` hash · `PO` Poseidon ·
`SH` SHA-256 · `FS` Fiat–Shamir · `P` parser · `R` runtime.

| Event | T | M | B | K | RS | CB | CC | TP | FE | H | PO | SH | FS | P | R |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| E01 | | | | | | | | | | | | | | ✓ | ✓ |
| E02 | | | | | | | | | | | | | | ✓ | |
| E03 | | | | | | | | | | | | | | ✓ | |
| E04 | | | | | | | | | | | | | | ✓ | |
| E05 | | | | | | | | | | | | | | ✓ | |
| E06 | ✓ | ✓ | | | | | | | | ✓ | | ✓ | | ✓ | |
| E07 | ✓ | | | | | | | | | ✓ | | ✓ | | ✓ | ✓ |
| E08 | ✓ | | | | | | | | | ✓ | | ✓ | ✓ | | |
| E09 | ✓ | ✓ | | ✓ | | | | | | ✓ | | ✓ | ✓ | | ✓ |
| E10 | ✓ | | | | | | | | | ✓ | | ✓ | ✓ | | |
| E11 | ✓ | | | | | | | | | | | | ✓ | | |
| E12 | ✓ | | | | | | | | | | | | | ✓ | |
| E13 | ✓ | | | | | ✓ | | | ✓ | | | | | | |
| E14 | | | | | | | | | | | ✓ | | | ✓ | |
| E15 | ✓ | | | | | ✓ | | | | | ✓ | | | | |
| E16 | | ✓ | | ✓ | | ✓ | | | | | | | | | |
| E17 | ✓ | | | ✓ | | ✓ | | | ✓ | | | | | | |
| E18 | | | | ✓ | | ✓ | | | | | | | | ✓ | |
| E19 | ✓ | ✓ | ✓ | | | | | | | | | | | | |
| E20 | ✓ | | ✓ | | ✓ | | | | | | | | | ✓ | |
| E21 | | | | | ✓ | | | | | | | | | ✓ | |
| E22 | ✓ | | | | ✓ | | | | | | | | ✓ | | |
| E23 | ✓ | | | | ✓ | | | | | | | | ✓ | | |
| E24 | ✓ | | | | ✓ | ✓ | ✓ | ✓ | ✓ | | | | | | |
| E25 | ✓ | | | | ✓ | | | | | | | | | ✓ | |
| E26 | ✓ | | | | ✓ | | | | | | | | | ✓ | |
| E27–E32 | ✓ | | | | | | | | | ✓ | | ✓ | ✓ | | |
| E33 | ✓ | | | | | | | | | | | | | ✓ | |
| E34 | ✓ | ✓ | | | | | | | | ✓ | | ✓ | ✓ | | |
| E35 | ✓ | | | | | | | | | ✓ | | ✓ | ✓ | | |
| E36 | ✓ | | | | | | | | | | ✓ | | | | |
| E37 | | ✓ | | ✓ | | | | | | ✓ | | ✓ | | ✓ | |
| E38 | | ✓ | | | | | | | | | | | | ✓ | |
| E39 | ✓ | ✓ | ✓ | | | | | | | | | | | | |
| E40–E42 | ✓ | ✓ | | | | | | ✓ | | | | | | | |
| E43 | | | | | ✓ | | | ✓ | ✓ | | | | | | |

`SH` is marked wherever the hash instance matters: the verifier's hash is
`crate::verify::sbf_hashv` (`v5_cu_probe.rs:2394`), passed as `HashFn`. `PO` appears only through
`successor_point` / `xor12_point` (`v5_atomic_terminal.rs:16`) and the compiled atomic terminal.

---

## Part 4 — Theorem boundaries found by marker search

Search restricted to pre-`#[cfg(test)]` regions of the eight production files.

**P4.1 — `unsafe`: none.** No `unsafe` block appears in any V5 production file.

**P4.2 — Three named prover-side obligations (SOUNDNESS/LIVENESS assumptions, not
implementation).** These are `&str` constants; nothing in the verifier enforces them.

`crates/aspis-prover/src/v5_real_host_proof.rs:150-151`:
```rust
pub const V5_PUBLIC_FS_SALT_PRODUCTION_OBLIGATION: &str =
    "sample each public FS salt freshly and independently after its corresponding PCS root is fixed and before the first dependent challenge";
```
`crates/aspis-prover/src/v5_spend_messages.rs:101-102`:
```rust
pub const V5_B_PIVOT_PAD_PRODUCTION_OBLIGATION: &str =
    "sample the Component-B inactive pivot pad freshly and independently before committing C2";
```
`crates/aspis-prover/src/v5_real_host_proof.rs:90-91`:
```rust
pub const V5_REAL_HOST_GOOD_RETRY_FRESHNESS_OBLIGATION: &str =
    "each retry derives a fresh schedule triple from public witness-independent transcript entropy";
```
Plus `v5_real_host_proof.rs:95-96`:
```rust
pub const V5_PRODUCTION_OS_ENTROPY_ASSUMPTION: &str =
    "every getrandom draw used by a v5 attempt is fresh, mutually independent, and uniformly distributed; entropy failure aborts without a deterministic fallback";
```
Classification: **soundness assumption** for the salt and retry-freshness obligations (they
condition E09 and E34); **liveness/hiding assumption** for the OS-entropy assumption; the pivot
pad conditions E16/E18. `V5_REAL_HOST_GOOD_RETRY_CAP = 17` (`v5_real_host_proof.rs:86`) is a
**liveness** bound — the deployed verifier contains no attempt-cap check.

**P4.3 — `panic!` in the deployed verifier: two sites, both index-bound assertions.**
`v5_cu_probe.rs:1242` `panic!("invalid v5 public Fiat-Shamir salt bounds")` and `:1250`
`panic!("invalid v5 root bounds")`. Both are reached only if the fixed prefix layout constants
are inconsistent, which the `const _: () = assert!(...)` block at `:217-232` forbids at compile
time. Classification: **implementation only**.

**P4.4 — `.expect(...)` in the deployed verifier: three sites.**
`v5_fri_checks.rs:140` ("fixed v5 claim count established by constructor"), `:324` ("successful
fixed-count transcript sampling"), `v5_cu_probe.rs:1775` ("the pinned copy-inactive functional is
nonzero"). All three are **implementation only**.

**`v5_relation_stress.rs:270` is NOT in the deployed path.** It sits at line 270, inside
`build_v5_relation_stress_tail_for_initial_claim`, which begins at line 201 under
`#[cfg(not(target_os = "solana"))]` (line 200) — a host-side *builder*, EXCLUDED from the SBF.
Verified absence of any inverse in the deployed relation path:

```
$ awk 'NR>=139 && NR<=198' v5_relation_stress.rs | grep -E "\.inv\(\)|inverse"   # verify_v5_relation_stress_with_additive
NONE
$ awk 'NR>=1223 && NR<=1245' crates/aspis-core/src/sumcheck.rs | grep -E "\.inv\(\)|inverse"   # WeightAccumulator::fold
NONE
```

Consequence for Q-ZERO: **there is no α-inverse and no panic risk at α = 0 in the deployed
verifier.** `WeightAccumulator::fold` (`sumcheck.rs:1223-1239`) computes α, α², α³ and folds; at
α = 0 that is a well-defined fold, not a fault. Q-ZERO is therefore purely an *algebraic*
soundness question, not a liveness or crash question. P4.6 stands unchanged.

**P4.5 — `debug_assert!`: three sites, all compiled out in release.**
`v5_cu_probe.rs:1779`, `:1877`, `v5_fri_checks.rs:172` (`debug_assert!(count == 3 || count == 4)`).
Classification: **implementation only**, but note they are *not* active in the deployed SBF, so
none constrains an adversary.

**P4.6 — Declared-but-unconstructed error variants.** `V5RelationStressError::ZeroMix` and
`::ZeroAlpha` (`v5_relation_stress.rs:47-48`) are never returned by
`verify_v5_relation_stress_with_additive`. Classification: **protocol assumption made silently** —
a certificate must either add an event for zero mix/α or prove the identities survive it.

**P4.7 — `verify_v5_reserved_tail` word-decoding is exactly equivalent to a byte-wise all-zero
check. RESOLVED.** `verify_v5_reserved_tail` (`v5_cu_probe.rs:1360-1365`) delegates to
`v5_reserved_tail_is_zero` (`:1335-1357`):

```rust
fn v5_reserved_tail_is_zero(bytes: &[u8]) -> bool {
    if bytes.len() != V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES {
        return false;
    }
    let mut offset = 0;
    while offset < V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES {
        let word = u64::from_le_bytes([
            bytes[offset], bytes[offset + 1], bytes[offset + 2], bytes[offset + 3],
            bytes[offset + 4], bytes[offset + 5], bytes[offset + 6], bytes[offset + 7],
        ]);
        if word != 0 {
            return false;
        }
        offset += 8;
    }
    true
}
```

A little-endian `u64` is zero iff all eight of its bytes are zero; the length is pinned to
`V5_CU_REAL_PREFIX_ZERO_TAIL_BYTES = 400` (`v5_cu_probe.rs:212`) and 400 = 50 × 8 exactly, so
every byte is covered with no remainder. The predicate is therefore **exactly** byte-wise
all-zero. The repository also carries a differential oracle
`verify_v5_reserved_tail_bytewise` (`v5_cu_probe.rs:3385-3391`, test-only) exercised at six sites
(`:3701, 3710, 3728, 3745, 3753, 3762`). Classification: **implementation only**. **E05 is fully
enforced** and needs no additional lemma.

**P4.8 — `TODO` / `SAFETY` / `ASSUME` / `UNSAFE` markers: none** in the eight production files.

---

## Part 5 — Every challenge

| Name | Type | Field | Zero allowed? | Sampled by | Absorb point that precedes it | Used at | Algebraic role | If zero |
|---|---|---|---|---|---|---|---|---|
| `lambda` | scalar | QM31 | **yes** | `challenge_qm31` (`transcript.rs:307`) | C1 root record (`:1428`) | `v5_atomic_terminal.rs:306` | atomic-v3 terminal mixer | NOT DETERMINABLE — depends on the compiled terminal's dependence on λ |
| `chi` | scalar | QM31 | **yes** | `challenge_qm31` | after λ | `:307` | atomic-v3 terminal mixer | as above |
| `theta` | scalar | QM31 | **yes** | `challenge_qm31` (`state_only_sumcheck.rs:96`) | constraint registry + helper sum (`:94-95`) | `:308` | zerocheck constraint batching | constraint batching degenerates to a single constraint |
| `zerocheck_point[0..10]` | vector | QM31¹⁰ | **yes** | 10× `challenge_qm31` (`:97-100`) | as above | `:309` | zerocheck evaluation point | evaluation at a boundary point |
| `mu` | scalar | QM31 | **yes** | `challenge_qm31` (`:101`) | as above | `:310` | helper mixer | helper term drops out |
| `eta` | scalar | QM31 | **no** | `challenge_nonzero_qm31` (`state_only_hiding.rs:236-238`) | mask-claim record (`:235`) | `v5_atomic_terminal.rs:324`; context decode (`v5_cu_probe.rs:1495`) | masking coefficient in `masked = mask + η·real` | would make `masked = mask`, unbinding `real` — **excluded by the sampler** |
| `z[0..10]` | vector | QM31¹⁰ | **yes** | per-round sumcheck challenge (`state_only_sumcheck.rs:278`) | each round polynomial | sumcheck point; **GoodA/GoodB point** (`v5_cu_probe.rs:2404` → `v5_good_gate_probe.rs:1141`) | sumcheck folding + Good-gate matrices | NOT DETERMINABLE — Good-gate singularity at a zero coordinate not analysed |
| `gamma` | scalar | QM31 | **no** | `challenge_nonzero_qm31` (`v5_cu_probe.rs:1475-1477`) | terminal triple + batch nonce (`:1470-1474`) | 19-column batch (`v5_fri_checks.rs:149-161`) | PCS batching generator | all non-constant terms vanish — **excluded** |
| `kappa` | scalar | QM31 | **no** | `challenge_nonzero_qm31` (`:1483-1485`) | inactive claim (`:1479-1482`) | scale table `(1,κ,κ²)` (`:1488-1492`) | three-point relation batching | point 2 and 3 contributions vanish — **excluded** |
| circle OOD point ×2 (round 0) | point | QM31² on unit circle, `t ∉ CM31`, `1+t² ≠ 0` | n/a | `challenge_secure_circle_point` (`transcript.rs:382-395`) | previous round objects | `weights.add_circle_tensor` (`v5_relation_stress.rs:164`) | layer-0 OOD tensor | sampler rejects the degenerate parameters |
| line OOD point ×6 | scalar | QM31 ∖ CM31 | n/a | `challenge_ood_qm31` (`transcript.rs:365-378`) | previous OOD value | `weights.add_line_tensor` (`:168`) | later-layer OOD tensor | in-domain point excluded by construction |
| `mix` ×8 | scalar | QM31 | **yes** | `challenge_qm31` (`v5_cu_probe.rs:829-831`) | each OOD value | `running_claim += mix·value` (`v5_relation_stress.rs:170`) | OOD observation mixer | that observation contributes nothing — **not excluded**, and `ZeroMix` is never raised (P4.6) |
| `alpha[0..4]` | scalar | QM31 | **yes** | `challenge_qm31` (`v5_cu_probe.rs:849-851`) | round sumcheck + fold nonce | fold coefficients `[α, α², α³]` (`v5_fri_checks.rs:445-451`); `weights.fold(alpha)` | FRI fold + dual fold | `v5_relation_stress.rs:270` `.expect("nonzero QM31 alpha has an inverse")` — **not excluded by the sampler** (P4.4) |
| 18 query indices | vector | `[0, 2^17)` | n/a | `challenge_queries_without_replacement(18, 1<<17, 64)` (`transcript.rs:429-462`) | selector byte | layer-0 openings | query phase | duplicates rejected; exhaustion → `DrawLimitExhausted` |

Sampler internals worth a certificate's attention: `challenge_qm31` is per-limb rejection
sampling that rejects the single non-canonical word `P` and redraws from fresh blocks
(`transcript.rs:307-345`), bounded by `CHALLENGE_RETRY_LIMIT`; exhaustion is a *completeness*
rejection, never a zero fallback (`:349-358` for the nonzero variant).

---

## Part 6 — Batching, fully reconstructed

**Generator.** Exactly the scalar power sequence `(1, γ, γ², …, γ¹⁸)` — no richer structure.
`v5_fri_checks.rs:149-162`:

```rust
fn v5_gamma_powers(gamma: QM31) -> [QM31; V5_FRI_TOTAL_COLUMNS] {
    let mut powers = [QM31::ZERO; V5_FRI_TOTAL_COLUMNS];
    powers[0] = QM31::ONE;
    powers[1] = gamma;
    let mut exponent = 2;
    while exponent < V5_FRI_TOTAL_COLUMNS {
        powers[exponent] = if exponent & 1 == 0 {
            powers[exponent / 2].square()
        } else {
            powers[exponent - 1].mul(gamma)
        };
        exponent += 1;
    }
```

- **Powers used**: γ⁰ … γ¹⁸. **Highest power γ¹⁸.** **Number of lanes: 19.**
- **Field**: coefficients in QM31; γ ∈ QM31 ∖ {0}.
- **Mixed-field embedding**: C1 values are M31, multiplied into QM31 weights by
  `qm31_m31_dot4_prepared_limbs_4b_bytes::<16>` (`v5_fri_checks.rs:386-390`); C2 values are QM31,
  multiplied by `qm31_sum_products3_prepared` (`:401-406`). Weight assignment: C1 lane `i` ← `powers[i]`
  for `i` in 0..16; C2 helper `h` ← `powers[16 + h]` for `h` in 0..3 (`:249-258`).

**Lane semantics.** From `v5_atomic_terminal.rs:25-31` and `v5_spend_messages.rs:59-64`:

| Absolute lane | Field | Name | Committed? | Role |
|---|---|---|---|---|
| 0..16 | M31 | semantic C1 lanes | **yes**, C1 root | randomized semantic trace |
| 16 | QM31 | Hcopy | **yes**, C2 root | copy/lookup lane |
| 17 | QM31 | Component B | **yes**, C2 root | mask source; 4th opening is the terminal mask |
| 18 | QM31 | Component C | **yes**, C2 root | PCS-view mask; **not** a semantic-terminal input (`v5_atomic_terminal.rs:12`) |

**Lanes that exist as witness data but are never committed**: the ten q18 mask-only lanes. They
survive only as the legacy offset constant used to locate Hcopy
(`v5_atomic_terminal.rs:50-58`), and their legacy slots are filled with `QM31::ZERO`
(`:289-300`). The q18 lane `G` is likewise gone (`LEGACY_G_COLUMN = 27`, left zero).

**Lanes that disappear before commitment**: `hcopy_padding`, `sumcheck_mask`,
`component_b_pads`, `component_b_pivot_pad`, and the per-lane `component_a` `M31BlockMask`
values are prover inputs (`crates/aspis-prover/src/v5_real_host_proof.rs:259-276`) that are
absorbed into the committed lanes rather than committed as separate codewords. **No verifier
predicate constrains any of them.**

**Also batched, separately from the PCS**: the three-point relation scale table `(1, κ, κ²)`
(`v5_cu_probe.rs:1488-1492`) — a second, independent geometric generator of length 3 over
`V5_CU_PROBE_RELATION_POINTS = 3` (`v5_cu_probe.rs:149`). A certificate needs a term for this as
well as for γ.

---

## Part 7 — FRI

- **Domain**: `domain_log_size = 19`, `trace_log_size = 10` (`v5_fri_checks.rs:47-48`). Layer-0
  fibre universe `V5_PRIVATE_LAYER0_LEAVES = 1 << 17` (`v5_private_openings.rs:21`).
- **Arity**: 4. `parent = query >> 2`, slot `query & 3` (`v5_fri_checks.rs:489,494`).
- **Rounds**: `V5_FRI_ROUNDS = 4` (`:39`).
- **Fold schedule**: layer-0 circle→line by
  `normalized_circle_to_line_arity4_prepared_polynomial_refs(&combined, &alpha_powers[0], inv_2x, inv_2y)`
  (`:480-485`); layers 1→2, 2→3 by `check_fixed_line_transition_prepared_polynomial_powers`
  (`:526-533`); layer 3→final by `check_fixed_terminal_transition_prepared_polynomial_refs`
  (`:542-549`). Fold coefficients per round are `[α, α², α³]` (`:445-451`).
- **Per-round dimension**: section depths `[17, 17, 15, 13, 11]`, value widths
  `[256, 192, 64, 64, 64]` (`v5_private_openings.rs:24-25`).
- **Query schedule**: 18 indices, without replacement, universe 2¹⁷, draw cap 64
  (`v5_fri_checks.rs:315-319`), three selectable branches (`state_only_prefix.rs:165`).
- **OOD schedule**: 2 samples per round × 4 rounds = 8; round 0 circle, rounds 1–3 line
  (`v5_cu_probe.rs:786-812`). Layout offsets `v5_relation_stress.rs:27-39`;
  `V5_RELATION_STRESS_BYTES == 928` (`:41`).
- **Opening schedule**: `V5_FRI_OPENING_POINTS = 4` claims per lane
  (`v5_fri_checks.rs:37`; `V5_WIRE_CLAIMS_PER_LANE = 4`, `v5_wire_skeleton.rs:26`); the claim table
  is 4 × 19 × 16 = 1216 bytes (`v5_atomic_terminal.rs:35`).
  **RESOLVED — and "four opening points" is a misnomer.** There are **three points and one
  structured linear functional**. `crates/aspis-prover/src/v5_split_layer_zero.rs:212-213`:

```rust
    let points = [*z, binary_successor_point(z), xor12_point(z)];
    let terminal_covector = v5_structured_terminal_covector(z);
```

  and `evaluate_component_b_relation_claims` (`:188-206`):

```rust
    claims[0] = crate::multilinear_eval_extension(message, &points[0]);
    claims[1] = crate::multilinear_eval_extension(message, &points[1]);
    claims[2] = crate::multilinear_eval_extension(message, &points[2]);
    ...
    claims[V5_RELATION_POINT_CLAIMS] = terminal;   // dot with terminal_covector
```

  So claims 0–2 are multilinear evaluations at `z`, `binary_successor_point(z)`, `xor12_point(z)` —
  exactly the triple the verifier re-checks at `v5_atomic_terminal.rs:278-283` — and **claim 3 is a
  covector dot product, not an evaluation at any point**. For the Component-B lane, claim 3 is the
  mask term consumed by `masked = mask + η·real` (`v5_atomic_terminal.rs:316-327`). The deployed
  γ-batch nevertheless treats all four positionally as if they were four point claims
  (`v5_fri_checks.rs:260-274`). See OPEN QUESTION Q-FUNC below.
- **Terminal polynomial**: 4 QM31 coefficients (`V5_FRI_FINAL_COEFFICIENTS = 4`,
  `V5_FRI_FINAL_BYTES = 64`, `:40-41`).
- **Transition identities**: E39–E42 above.
- **Terminal identity**: two independent ones — the FRI terminal transition (E42) and the
  relation dot `weights·final + additive·final == running_claim` (E24) — tied together by the
  equality E43.

---

## Part 8 — Complete transcript table

`absorb(label, data)` = `state ← hash(state ‖ [0x00, label] ‖ data)` (`transcript.rs:272-274`);
`squeeze_block` = `out ← hash(state ‖ [0x01])`, then `state ← hash(state ‖ [DOM_ADVANCE])`
(`:283-286`). `DOM_ABSORB = 0x00`, `DOM_SQUEEZE = 0x01`, `DOM_GRIND = 0x03` (`:199-202`).

| Step | Op | Label (byte) | Bytes | Purpose | Challenge created | Future events |
|---|---|---|---|---|---|---|
| 1 | absorb | `PROFILE` (1) | 27 | `b"aspis-v5-real-witness-cu-v1"` (`v5_cu_probe.rs:1163`) | — | E10 |
| 2 | absorb | `M31_CIRCLE_BASIS` (11) | — | basis discriminator | — | E10 |
| 3 | absorb | `STATEMENT` (2) | 32 | live statement digest | — | E07 |
| 4 | absorb | `M31_CIRCLE_ROUND_ROOT` | 65 | `layer(0) ‖ c1_root ‖ salt0` | — | E06, E09, E19, E37 |
| 5 | squeeze | — | — | — | `lambda` | E15 |
| 6 | squeeze | — | — | — | `chi` | E15 |
| 7 | absorb | `M31_CIRCLE_C2_ROOT` (13) | 64 | `c2_root ‖ salt1` | — | E06, E09, E16, E37 |
| 8 | absorb | `M31_STATE_ONLY_CONSTRAINT_REGISTRY` | 26 | frozen constraint registry (`state_only_sumcheck.rs:83-94`) | — | E11 |
| 9 | absorb | `M31_STATE_ONLY_HELPER_SUM` | 16 | all-zero | — | E11 |
| 10 | squeeze | — | — | — | `theta` | E11, E15 |
| 11–20 | squeeze ×10 | — | — | — | `zerocheck_point[0..10]` | E11, E15 |
| 21 | squeeze | — | — | — | `mu` | E15 |
| 22 | absorb | `M31_STATE_ONLY_HIDING_MASK_CLAIM` (31) | 18 | `degree ‖ rounds ‖ initial_mask_claim` (`state_only_hiding.rs:231-235`) | — | E17 |
| 23 | squeeze | — | — | nonzero sampler | `eta` | E17 |
| 24–43 | absorb→squeeze ×10 | per-round | 10 × 448 | degree-27 semantic sumcheck | `z[0..10]` | E11, E12, E36 |
| 44 | absorb | `M31_CIRCLE_STATEMENT_POINTS` (14) | 480 | 3 × 10 point coordinates | — | E12, E14 |
| 45 | absorb | `M31_CIRCLE_STATEMENT_EVALUATIONS` (15) | 1216 | 4 × 19 claims | — | E12, E15, E16, E19 |
| 46 | absorb | `CLAIM` (6) | 48 | `real ‖ mask ‖ masked` | — | E13, E17 |
| 47 | absorb | `M31_PAYMENT_BATCH_POW_NONCE` (28) | 8 | batch nonce, checked first | — | **E27** |
| 48 | squeeze | — | — | nonzero sampler | `gamma` | E19, E20 |
| 49 | absorb | `SECOND_PHASE_CLAIM` (10) | 16 | inactive claim | — | E20, E24 |
| 50 | squeeze | — | — | nonzero sampler | `kappa` | E20 |

Then for `round` = 0,1,2,3 (`v5_cu_probe.rs:784-861`):

| Step | Op | Label | Bytes | Purpose | Challenge | Events |
|---|---|---|---|---|---|---|
| R.1 | squeeze | — | — | round 0 circle / rounds 1–3 line | OOD point (sample 0) | E21, E22, E25 |
| R.2 | absorb | `M31_CIRCLE_OOD_VALUE`(16) / `M31_LINE_OOD_VALUE`(17) | 16 + tag | OOD value 0 | — | E23, E25 |
| R.3 | squeeze | — | — | — | `mix` (sample 0) | E23, E25, E-ZERO |
| R.4 | squeeze | — | — | — | OOD point (sample 1) | E21, E22, E25 |
| R.5 | absorb | same | 16 + tag | OOD value 1 | — | E23, E25 |
| R.6 | squeeze | — | — | — | `mix` (sample 1) | E23, E-ZERO |
| R.7 | absorb | relation sumcheck | 112 | 7 coefficients | — | E23 |
| R.8 | absorb | `M31_CIRCLE_FOLD_POW_NONCE` (20) | 9 | `round ‖ nonce_le`, checked first | — | **E28–E31** |
| R.9 | squeeze | — | — | — | `alpha[round]` | E24, E26, E39–E42, E-ZERO |
| R.10 | absorb | `M31_CIRCLE_ROUND_ROOT` | 65 | later root `round+1` ‖ salt `round+2`; only when `round < 3` | — | E06, E09, E37, E40–E42 |

Then the final phase (`v5_fri_checks.rs:297-319`):

| Step | Op | Label | Bytes | Purpose | Challenge | Events |
|---|---|---|---|---|---|---|
| F.1 | absorb | `M31_CIRCLE_FINAL_TENSOR_POLY` (19) | 64 | 4 final coefficients | — | E42, E43 |
| F.2 | — | (PoW check) | — | `grinding_ok(final_nonce, 32)` | — | **E32** |
| F.3 | absorb | `GRIND_NONCE` (5) | 8 | final nonce | — | E32 |
| F.4 | absorb | `M31_STATE_ONLY_QUERY_CANDIDATE` (44) | **1** | selector byte | — | **E33, E34** |
| F.5 | squeeze | — | — | 18 draws, no replacement, cap 64 | query schedule | E35, E36, E38, E39 |

**Total absorbs**: 20 in the prefix, 4 per relation round (×4 = 16, of which the later-root absorb
occurs only in rounds 0–2, so 15), 3 in the final phase — **38 absorbs**.
**Total squeeze sites**: 17 in the prefix, 6 per relation round (24), 1 in the final phase —
**42 squeeze sites** (each `challenge_qm31` may consume more than one block under rejection).

**Boundary numbering is not asserted.** The source contains no boundary enumeration. Under the
convention *one boundary = one maximal absorb run immediately followed by ≥1 squeeze*, the count
is 28 (15 prefix + 12 relation + 1 final). A different convention yields a different number; a
certificate must state its own and derive `R` from it. See NOT DETERMINABLE N1.

---

## Part 9 — Minimal theorem set

For each predicate class, the theorem that would license replacing it with a probability.

| Tag | Predicate class | Theorem required | Status |
|---|---|---|---|
| **T-RO** | every challenge (E08) | Random-oracle model for `sbf_hashv`; SHA-256 instantiation | imported |
| **T-FS** | whole-transcript soundness | BCS / state-restoration Fiat–Shamir for a multi-round IOP, instantiated at this protocol's boundary count | imported; **`R` must be re-derived**, see N1 |
| **T-MERK** | E37, E06 | Merkle binding for **salted radix-4 leaves under a binary-cap topology** with five distinct tree tags | imported, but the salted/radix-4/cap combination must be checked against the cited statement |
| **T-CANON** | E04 | Canonical-encoding injectivity for M31/QM31 LE bytes | elementary |
| **T-SUM27** | E11 | Round-by-round sumcheck soundness for ten rounds at degree 27 | imported |
| **T-SUM6** | E23 | Round-by-round sumcheck soundness for four rounds at 7 coefficients | imported |
| **T-MCA19** | E19 | **Mutual-correlated-agreement / proximity-gap for a 19-term scalar-powers generator whose lanes mix an M31 block and a QM31 block** | **new — the q18 statement is for a different width and a different base/extension split** |
| **T-JOHN** | E39 | Johnson-regime list decoding at message 2¹⁰ / domain 2¹⁹, plus circle→line transport at arity 4 | imported |
| **T-WHIR** | E40–E42 | Fold-list commutation across three line layers and the terminal transition | imported |
| **T-OOD** | E22 | OOD-sampling lemma: domain ⊂ CM31, so `c1 ≠ 0` puts the point out of domain by construction (`transcript.rs:365-378`) | **provable from the sampler; state it** |
| **T-CIRC** | E21 | Circle membership `x² + y² = 1` and the rational parametrisation's exclusion of `t ∈ CM31`, `1 + t² = 0` (`transcript.rs:382-395`) | **provable from the sampler; state it** |
| **T-PI** | E12, E17, E20, E24 | Polynomial-identity (Schwartz–Zippel) over QM31 at the stated degrees | imported |
| **T-CB** | E15 | **Component-B terminal lemma**: the compiled unmasked atomic-v3 terminal at 19 lanes, with legacy mask-only and G slots zero, equals the intended relation | **new — q18's terminal is the masked 28-column evaluator** |
| **T-CC** | E24 | **Component-C terminal lemma**: the compact degree-27 additive covector shares the four dual folds and the final dot correctly (`V5RelationStressAdditive`, `v5_relation_stress.rs:67-70`) | **new** |
| **T-ZERO-SLOT** | E18 | **Legacy-slot-zero lemma**: leaving legacy slots 16..26 and 27 zero does not admit a terminal value the masked evaluator would reject | **new — enforced by code shape, not by a predicate** |
| **T-PT** | E14 | Poseidon2 point-structure lemma: `successor_point` and `xor12_point` are the intended maps and the triple is rigid | **new for V5** |
| **T-GOOD** | E36 | **GoodA/GoodB non-singularity lemma**: 12×12 over M31 and 4×4 over QM31, built from `K(X) = prod_i (X² − x_i²)` and the sumcheck point | **new — q18's Good product is a different object** |
| **T-SEL** | E34 | **Three-branch selector-scope lemma with no leastness premise**, given that the selector is absorbed after the final nonce and only the selected branch is checked | **new — q18's lemma assumes all three evaluated and least selected** |
| **T-QWR** | E35 | Query-phase bound for sampling without replacement with a bounded draw cap | imported |
| **T-GRIND** | E27–E32 | Grinding/leading-zero bound in the RO model at six independent boundary positions | imported |
| **T-PARSE** | E01–E03, E05, E33, E38 | Parser correctness: the accepted grammar admits exactly one interpretation per byte string | **new; also see P4.7** |
| **T-STMT** | E07 | Collision resistance of the statement digest, and equality of the wrapper-reconstructed statement with the proof-carried context | imported |
| **Q-ZERO** | α and `mix` | **Open, narrowed.** α and `mix` are drawn with `challenge_qm31`, which permits zero (`transcript.rs:307-345`). There is **no inverse and no panic** in the deployed path (P4.4), so this is purely algebraic: does α = 0 or `mix` = 0 admit a false accept through `WeightAccumulator::fold` (`sumcheck.rs:1223-1239`), `evaluate`, or `running_claim += mix·value` (`v5_relation_stress.rs:170`)? `ZeroMix`/`ZeroAlpha` are declared but never raised (P4.6). | **new, unresolved** |
| **Q-FUNC** | E19, E16 | **Open**: claim 3 of every lane is a covector dot product, not a point evaluation (Part 7), yet the γ-batch weights all four positionally (`v5_fri_checks.rs:260-274`). Does the MCA/proximity statement being relied on cover a batch in which one of the four "opening" slots is a structured linear functional of the message rather than an evaluation? | **new, unresolved** |
| **Q-SINK** | E-SINK | **Open**: is `fri_sum + relation_claim + terminal_masked` meant to satisfy an identity? It is discarded (`v5_cu_probe.rs:2420,2462-2464`). | **new, unresolved** |
| **T-EXTR** | knowledge soundness | Extractor for the spend relation; not exercised by any predicate above | out of scope of this extraction |
| **T-SIM** | hiding | Simulator; **no V5 hiding artifact exists** (see N3) | out of scope |

---

## Part 10 — Can the q18 certificate be reused?

**No, not as a whole.** A mapping was proved only for the six work events. Classification of every
q18 `soundness.terms_bits` entry from `results/spend/spend_d_after_g_soundness_epro.json`:

| q18 term | Class | Why |
|---|---|---|
| `polynomial_batch_width_29` | **CHANGED** | q18 batches 29 lanes to γ²⁸ (`generator_order` = `"semantic[0..16], mask-only[16..26], H[26], G[27], D[28]"`). V5 batches 19 to γ¹⁸ (`v5_fri_checks.rs:149-161`), with a different M31/QM31 split. New term required (T-MCA19 → E19). |
| `four_fold_union` (4 rows) | **IDENTICAL in structure, requires re-derivation** | Same arity 4, same four rounds, same fold work 34/33/30/25 (`v5_cu_probe.rs:641-648`). But each row's degree input depends on the batched width, which changed. Map to E39–E42 only after T-MCA19 fixes the width. |
| `final_q18_miss_times_3` | **CHANGED** | Same 18 queries without replacement and same three branches, but the verifier no longer checks leastness (`v5_cu_probe.rs:958-976`). q18's `selector_scope_proof` records `"all_three_post_final_schedules_evaluated": true` and `"selection_rule": "least selector satisfying the exact complete-Good product"`. New lemma required (T-SEL → E34). |
| `two_sample_ood_list_union` | **SPLIT** | V5 draws 8 OOD samples: 2 circle (round 0) + 6 line (rounds 1–3), with different samplers (`v5_cu_probe.rs:786-812`). q18's single union term must split into a circle term and a line term. |
| `relation_ood_mixers_24` | **CHANGED** | V5 has 8 mixers, not 24, and they are drawn with plain `challenge_qm31` so zero is permitted (Q-ZERO). |
| `nonzero_gamma_and_three_point_batch_30` | **SPLIT** | V5 has two independent batching generators: γ⁰…γ¹⁸ over 19 PCS lanes and `(1, κ, κ²)` over 3 relation points (`v5_cu_probe.rs:1488-1492`). One q18 term covers both in V5's predecessor; V5 needs two. |
| `copy_inactive_nonzero_gamma_28` | **CHANGED** | Width 28 → the Hcopy lane is now C2 lane 16 of 19 (`v5_atomic_terminal.rs:26`); the copy-inactive functional is at `v5_cu_probe.rs:1775`. |
| `atomic_tuple_compression` | **NOT DETERMINABLE** | Whether the compiled unmasked terminal preserves q18's tuple-compression degree is not answerable without reading `atomic_state_only_selected_unmasked_terminal_value_compiled_v3`. |
| `atomic_copy_range_poles` | **NOT DETERMINABLE** | Same reason. |
| `atomic_theta_collision` | **IDENTICAL candidate** | θ is still one `challenge_qm31` batching all constraints (`state_only_sumcheck.rs:96`) with the same registry. Verify the constraint count is unchanged before reusing. |
| `zerocheck_equality_point` | **IDENTICAL candidate** | Same ten-coordinate zerocheck point, same registry (`state_only_sumcheck.rs:97-100`). |
| `zero_sum_h1_helper` | **DELETED** | The H1/G lanes are gone. `LEGACY_G_COLUMN` is left zero (`v5_atomic_terminal.rs:53,289-300`); the helper sum absorb is a fixed all-zero 16 bytes (`state_only_sumcheck.rs:95`). |
| `mask_original_nonzero_eta` | **CHANGED** | η still nonzero-sampled (`state_only_hiding.rs:236-238`), but its algebraic role is now the single identity `masked = mask + η·real` against Component B's 4th opening (`v5_atomic_terminal.rs:324`), not ten mask-only lanes. New term (T-CB, E17). |
| `ten_degree_27_zerocheck_rounds` | **IDENTICAL** | `STATE_ONLY_SUMCHECK_ROUNDS = 10`, `DEGREE = 27` unchanged (`state_only_sumcheck.rs:13-14`), same streaming verifier (`:257-286`), same absorb path. Maps to E11. |
| `poseidon2_assumption` | **CHANGED** | V5 uses Poseidon2 in a *new* place: the point-structure identities `successor_point` / `xor12_point` (`v5_atomic_terminal.rs:278-283`). Needs T-PT in addition to the policy reserve. |
| `sha256_rom_assumption` | **IDENTICAL** | Same `HashFn`, same duplex construction, same domain bytes (`transcript.rs:199-202`). |
| Six work thresholds (`batch_work_bits`, `fold_work_bits`, `final_work_bits`) | **IDENTICAL — proved** | q18: 37 / [34,33,30,25] / 32. V5: `v5_cu_probe.rs:636-648`, `:652-654` return the same literals; `v5_fri_checks.rs:306` uses `STATE_ONLY_SPEND_GRINDING_BITS`. Same predicate `grinding_ok` (`transcript.rs:472-475`), same `DOM_GRIND`, same digest input, same check-before-absorb ordering. Maps to E27–E32. **Caveat P4.6/P4.4 does not affect these.** |

**New events with no q18 counterpart**: E14 (point-structure triple), E16 (Component-B mask
opening), E18 (legacy-slot-zero), E21 (circle membership), E24 (dual-fold terminal dot with the
Component-B covector), E36 (GoodA/GoodB at 12×12 / 4×4), E-SINK, E-ZERO.

**Merged**: none found.

**Bottom line for a certificate author.** Exactly one q18 group — the six work thresholds — is
proved identical. Two more (`ten_degree_27_zerocheck_rounds`, `sha256_rom_assumption`) are
identical on the evidence above. Everything that touches lane count, masking, the terminal, the
selector, or the OOD schedule must be recomputed, and five theorems in Part 9 are marked **new**.

---

## NOT DETERMINABLE FROM SOURCE

**N1 — The boundary count `R` for the Fiat–Shamir instantiation.** No file enumerates boundaries.
Part 8 gives 38 absorbs / 42 squeeze sites and a count of 28 under one stated convention.
*Would be answered by*: a round-boundary certificate artifact for V5. None exists in the
repository.

**N2 — The semantic role of each individual C1 column.** Still open. The verifier treats them as a
16-wide M31 vector (`v5_fri_checks.rs:386-390`). The transcript-absorbed constraint registry
records `STATE_ONLY_SEMANTIC_SOURCE_LANES = 95` (`state_only_sumcheck.rs:22`, absorbed at
`:86`), which is a source-lane count and **not** a per-column role map for the 16 committed
columns. *Would be answered by*: `crates/aspis-statement/src/atomic_state_only_trace.rs`.

**N3 — Whether V5's masking inputs suffice, and under what condition.** The deployed verifier
checks no masking-rank or hiding condition; the inputs are prover-side
(`v5_real_host_proof.rs:259-276`) and two of them carry only `&str` obligations (P4.2).
*Would be answered by*: a V5 hiding/masking certificate. `release/aspis-v5-tag67-mainnet-v1/`
contains no `certificates/` directory.

**N4 — The internals of `atomic_state_only_selected_unmasked_terminal_value_compiled_v3`**, hence
the exact degrees behind E15 and the q18 rows `atomic_tuple_compression` and
`atomic_copy_range_poles`. *Would be answered by*:
`crates/aspis-statement/src/atomic_state_only_terminal.rs`.

**N5 — RESOLVED.** The four claims per lane are three multilinear evaluations at
`z`, `binary_successor_point(z)`, `xor12_point(z)` plus one structured covector dot product —
not four points. See Part 7 and `crates/aspis-prover/src/v5_split_layer_zero.rs:188-215`. The
consequence for batching is recorded as OPEN QUESTION Q-FUNC.

**N6 — RESOLVED.** Word-decoding is exactly equivalent to a byte-wise all-zero check; see P4.7.
E05 is fully enforced.

**N7 — Narrowed, still open** (Q-ZERO). The crash/inverse half is resolved: no inverse and no
panic exist in the deployed path (P4.4). What remains is purely algebraic — whether α = 0 or
`mix` = 0 admits a false accept. *Would be answered by*: a lemma about `WeightAccumulator::fold`
(`crates/aspis-core/src/sumcheck.rs:1223-1239`) and `evaluate` at α = 0, plus the intended
semantics of the unraised `ZeroAlpha`/`ZeroMix` variants.

**N8 — Whether the discarded composite sum was meant to be checked** (Q-SINK). *Would be answered
by*: a design note or a V5 relation-composition lemma. Nothing in the repository states an
intended identity for it.

---

*Extraction from source only. No probability, bit count, or security level is computed, estimated,
or asserted anywhere in this document. Every classification in Part 10 that is not marked
"proved" is a structural comparison, not a numerical claim.*
