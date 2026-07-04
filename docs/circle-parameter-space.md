# Circle parameter space

Generated: 2026-04-20T08:40:24.701570+00:00

Pinned reference: `uni_stark_circle_v1.postcard` at `0f87f2b543a01880274965c410bf804c124f5046`.

## Actual knobs

- Hash family is generic at the CirclePcs type level, but the shipped Circle examples at the pinned commit only instantiate Keccak and Poseidon2 MMCS/challenger combinations; no SHA-256 Circle configuration is provided out of the box.
- log_blowup is the actual rate knob. p3-fri exposes any usize value, with blowup = 2^log_blowup and conjectured soundness bits = log_blowup * num_queries + query_proof_of_work_bits.
- Query count is a direct knob. p3-circle does not expose 100/120/128-bit presets; those targets have to be reached by choosing num_queries, log_blowup, and query_proof_of_work_bits together.
- max_log_arity is exposed in FriParameters, but Circle folding hard-asserts log_arity == 1 at this commit. In practice Circle PCS is fixed to arity 2, so max_log_arity > 1 is not a real supported range.
- log_final_poly_len is exposed in FriParameters, but circle/src/prover.rs explicitly says Circle folds down to blowup elements with no separate final_poly_len. For the Circle path this knob is narrower than it appears.
- query_proof_of_work_bits is live in the Circle prover/verifier and can trade prover grinding for fewer queries at a fixed conjectured target.
- commit_proof_of_work_bits is exposed in FriParameters but not consumed by the Circle prover/verifier path, so it is not a live cost/security knob for Circle proofs at this commit.
- CirclePcs cannot commit to fewer than 4 rows. That makes 4 the minimum meaningful trace height for this protocol implementation.
- The field tower in the validated path is M31 / CM31 / QM31. Circle code is generic over ComplexExtendable base fields, but the shipped proof examples and the earlier byte-level mirror verifier are both pinned to the Mersenne31 cubic-extension family.
- Security accounting exposed by p3-fri is conjectural only. The code offers conjectured_soundness_bits(); it does not expose separate Johnson / unique-decoding / capacity security selectors for Circle STARKs.

## Measured scope

- Measured hash family: `Keccak256 byte-digest MMCS + HashChallenger`
- Measured sweep keeps the validated mirror proof family from the earlier interop spike: M31 base field, cubic extension challenge field, Keccak-256 commitments/transcript, postcard proof bytes.
- Poseidon2 and the u64-sponge Keccak example families are documented as exposed by p3-circle, but they are not swept here because the current mirror verifier was validated only against unchanged Keccak-256 byte-digest proofs. Supporting a different MMCS/challenger family would require new proof-type plumbing rather than a pure parameter change.

## Primary sources

- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/fri/src/config.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/pcs.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/prover.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/folding.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/verifier.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/examples/src/types.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/examples/src/proofs.rs
- https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/examples/examples/prove_prime_field_31.rs
