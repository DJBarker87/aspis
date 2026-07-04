# WHIR-UD Spike Gate

Conclusion: **AMBER**

Selected configuration for the gate decision: `whir-ud-goldilocks2-t100-rate1over4-d18-e1-l0-i4-k4-affine3x5`

## Rationale

- Direct SBF compilation failed for the wrapper program, so there is no proven compilation path yet.
- Largest successfully round-tripped trace in this sweep used 2^18 coefficients.
- Smaller toy traces produce lower hash-only floors, but the gate is evaluated on the largest trace reached in the sweep: whir-ud-goldilocks2-t100-rate1over4-d18-e1-l0-i4-k4-affine3x5.
- Best hash-only lower bound is 499648 CU for whir-ud-goldilocks2-t100-rate1over4-d18-e1-l0-i4-k4-affine3x5 at 2^18 coefficients and 163680 bytes.
- Even the best measured proof needs at least 133 staged transactions just to upload raw bytes.

## Projection Context

- Compilation status: `failed`.
- Raw build logs: [results/whir-ud-spike/raw/sbf/build.stdout](/Users/dominic/ZK/results/whir-ud-spike/raw/sbf/build.stdout) and [results/whir-ud-spike/raw/sbf/build.stderr](/Users/dominic/ZK/results/whir-ud-spike/raw/sbf/build.stderr).
