# Circle parameter gate

## RED

### Best configuration

- `counter4-t100-rate1over2-q84-pow16-arity1` scenario=`counter4` target_bits=`100` rate=`1/2` queries=`84` query_pow_bits=`16` projected_cu=`12144181` proof_bytes=`43149`

- Soundness lower bound=`58.0` upper bound=`100.0` target=`100.0`

### Rationale

- Best projected configuration is `counter4-t100-rate1over2-q84-pow16-arity1` at 12144181 CU with proof size 43149 bytes.
- That leaves -10744181 CU against the 1.4M cap.
- Every successful configuration still exceeds the 1232-byte transaction ceiling and therefore requires staged upload.
- Soundness accounting for the best configuration is split: proven lower bound 58.0 bits, conjectured upper bound 100.0 bits.
- No defensible configuration gets within 2x of the compute cap, so the gap is structural rather than a bad parameter choice.

### Recommendation

Move to the WHIR-UD spike. The remaining Circle gap is structural across the supported p3-circle configuration space measured here.
