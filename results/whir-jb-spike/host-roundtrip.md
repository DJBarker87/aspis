# WHIR-JB Host Roundtrip

Generated: `2026-04-20T10:18:04.177758+00:00`

Reference: `https://github.com/WizardOfMenlo/whir` at `0aeaa7f337c743d9ddfcb9d909628d6491e3355c`

Field selection: Goldilocks3 + Johnson-bound WHIR is the frozen exact-upstream target for this parity phase.

## Notes

- Current upstream Merkle/PoW hash mode observed through the host crate: Blake3.
- Reference and mirror verifiers both operate directly on the exact upstream proof byte streams (`narg_string` and `hints`) without any wrapper-level rewriting.
- Transcript parity is measured byte-for-byte over Shake128 sponge absorb/squeeze traffic, with final-claim equality checked separately.

## Attempt Matrix

| id | status | achieved bits | d | rate | proof bytes | ref hashes | mirror hashes | parity | variants |
| --- | --- | ---: | ---: | --- | ---: | ---: | ---: | --- | --- |
| whir-jb-goldilocks3-dev-t100-rate1over16-d8-e1-l0-i4-k4-affine3x5 | ok | 100.00 | 8 | 1/16 | 18920 | 243 | 243 | a=yes s=yes r=yes f=yes | 4/4 |
| whir-jb-goldilocks3-gate-t128-rate1over16-d20-e1-l0-i4-k4-quadratic7 | ok | 128.00 | 20 | 1/16 | 98496 | 2089 | 2089 | a=yes s=yes r=yes f=yes | 4/4 |

## Divergences

- None.

## Raw Artifacts

- `whir-jb-goldilocks3-dev-t100-rate1over16-d8-e1-l0-i4-k4-affine3x5`: `results/whir-jb-spike/raw/host-roundtrip/whir-jb-goldilocks3-dev-t100-rate1over16-d8-e1-l0-i4-k4-affine3x5/valid.narg.bin` and `results/whir-jb-spike/raw/host-roundtrip/whir-jb-goldilocks3-dev-t100-rate1over16-d8-e1-l0-i4-k4-affine3x5/valid.hints.bin`
- `whir-jb-goldilocks3-gate-t128-rate1over16-d20-e1-l0-i4-k4-quadratic7`: `results/whir-jb-spike/raw/host-roundtrip/whir-jb-goldilocks3-gate-t128-rate1over16-d20-e1-l0-i4-k4-quadratic7/valid.narg.bin` and `results/whir-jb-spike/raw/host-roundtrip/whir-jb-goldilocks3-gate-t128-rate1over16-d20-e1-l0-i4-k4-quadratic7/valid.hints.bin`
