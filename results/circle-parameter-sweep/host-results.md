# Circle host parameter sweep

Generated: 2026-04-20T08:40:26.734638+00:00

Attempts: `90` success: `20` failed: `70` divergences: `0`.

## Summary

- Successful attempts only occurred at `log_blowup=1` (`rate=1/2`). Every measured `log_blowup > 1` configuration failed before proof emission.
- All successful proofs were accepted by both the p3-circle reference verifier and the unchanged mirror verifier.
- Successful `max_log_arity` variants emitted byte-identical proofs, so `max_log_arity > 1` was inert rather than providing higher-arity folding.

- The explicit `log_final_poly_len=2` and `commit_proof_of_work_bits=8` probes matched the baseline `rate=1/2`, `pow16`, `target=100` proof byte-for-byte, confirming that both knobs are inert on the measured Circle path.

## Matrix

| id | scenario | target | rate | queries | q_pow | max_arity | status | proof_bytes | ref | mirror | notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `counter4-t100-rate1over2-q92-pow8-arity1` | `counter4` | `100` | `1/2` | `92` | `8` | `1` | `success` | `47234` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t100-rate1over2-q84-pow16-arity1` | `counter4` | `100` | `1/2` | `84` | `16` | `1` | `success` | `43149` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t100-rate1over2-q92-pow8-arity2` | `counter4` | `100` | `1/2` | `92` | `8` | `2` | `success` | `47234` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t100-rate1over2-q84-pow16-arity2` | `counter4` | `100` | `1/2` | `84` | `16` | `2` | `success` | `43149` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t100-rate1over2-q92-pow8-arity3` | `counter4` | `100` | `1/2` | `92` | `8` | `3` | `success` | `47234` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t100-rate1over2-q84-pow16-arity3` | `counter4` | `100` | `1/2` | `84` | `16` | `3` | `success` | `43149` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t100-rate1over4-q46-pow8-arity1` | `counter4` | `100` | `1/4` | `46` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over4-q42-pow16-arity1` | `counter4` | `100` | `1/4` | `42` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over4-q46-pow8-arity2` | `counter4` | `100` | `1/4` | `46` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over4-q42-pow16-arity2` | `counter4` | `100` | `1/4` | `42` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over4-q46-pow8-arity3` | `counter4` | `100` | `1/4` | `46` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over4-q42-pow16-arity3` | `counter4` | `100` | `1/4` | `42` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over8-q31-pow8-arity1` | `counter4` | `100` | `1/8` | `31` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over8-q28-pow16-arity1` | `counter4` | `100` | `1/8` | `28` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over8-q31-pow8-arity2` | `counter4` | `100` | `1/8` | `31` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over8-q28-pow16-arity2` | `counter4` | `100` | `1/8` | `28` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over8-q31-pow8-arity3` | `counter4` | `100` | `1/8` | `31` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over8-q28-pow16-arity3` | `counter4` | `100` | `1/8` | `28` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over16-q23-pow8-arity1` | `counter4` | `100` | `1/16` | `23` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over16-q21-pow16-arity1` | `counter4` | `100` | `1/16` | `21` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over16-q23-pow8-arity2` | `counter4` | `100` | `1/16` | `23` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over16-q21-pow16-arity2` | `counter4` | `100` | `1/16` | `21` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over16-q23-pow8-arity3` | `counter4` | `100` | `1/16` | `23` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over16-q21-pow16-arity3` | `counter4` | `100` | `1/16` | `21` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over2-q112-pow8-arity1` | `counter4` | `120` | `1/2` | `112` | `8` | `1` | `success` | `57437` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t120-rate1over2-q104-pow16-arity1` | `counter4` | `120` | `1/2` | `104` | `16` | `1` | `success` | `53358` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t120-rate1over2-q112-pow8-arity2` | `counter4` | `120` | `1/2` | `112` | `8` | `2` | `success` | `57437` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t120-rate1over2-q104-pow16-arity2` | `counter4` | `120` | `1/2` | `104` | `16` | `2` | `success` | `53358` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t120-rate1over2-q112-pow8-arity3` | `counter4` | `120` | `1/2` | `112` | `8` | `3` | `success` | `57437` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t120-rate1over2-q104-pow16-arity3` | `counter4` | `120` | `1/2` | `104` | `16` | `3` | `success` | `53358` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t120-rate1over4-q56-pow8-arity1` | `counter4` | `120` | `1/4` | `56` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over4-q52-pow16-arity1` | `counter4` | `120` | `1/4` | `52` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over4-q56-pow8-arity2` | `counter4` | `120` | `1/4` | `56` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over4-q52-pow16-arity2` | `counter4` | `120` | `1/4` | `52` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over4-q56-pow8-arity3` | `counter4` | `120` | `1/4` | `56` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over4-q52-pow16-arity3` | `counter4` | `120` | `1/4` | `52` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over8-q38-pow8-arity1` | `counter4` | `120` | `1/8` | `38` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over8-q35-pow16-arity1` | `counter4` | `120` | `1/8` | `35` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over8-q38-pow8-arity2` | `counter4` | `120` | `1/8` | `38` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over8-q35-pow16-arity2` | `counter4` | `120` | `1/8` | `35` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over8-q38-pow8-arity3` | `counter4` | `120` | `1/8` | `38` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over8-q35-pow16-arity3` | `counter4` | `120` | `1/8` | `35` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over16-q28-pow8-arity1` | `counter4` | `120` | `1/16` | `28` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over16-q26-pow16-arity1` | `counter4` | `120` | `1/16` | `26` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over16-q28-pow8-arity2` | `counter4` | `120` | `1/16` | `28` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over16-q26-pow16-arity2` | `counter4` | `120` | `1/16` | `26` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over16-q28-pow8-arity3` | `counter4` | `120` | `1/16` | `28` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t120-rate1over16-q26-pow16-arity3` | `counter4` | `120` | `1/16` | `26` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over2-q120-pow8-arity1` | `counter4` | `128` | `1/2` | `120` | `8` | `1` | `success` | `61515` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t128-rate1over2-q112-pow16-arity1` | `counter4` | `128` | `1/2` | `112` | `16` | `1` | `success` | `57443` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t128-rate1over2-q120-pow8-arity2` | `counter4` | `128` | `1/2` | `120` | `8` | `2` | `success` | `61515` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t128-rate1over2-q112-pow16-arity2` | `counter4` | `128` | `1/2` | `112` | `16` | `2` | `success` | `57443` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t128-rate1over2-q120-pow8-arity3` | `counter4` | `128` | `1/2` | `120` | `8` | `3` | `success` | `61515` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t128-rate1over2-q112-pow16-arity3` | `counter4` | `128` | `1/2` | `112` | `16` | `3` | `success` | `57443` | `accept` | `accept` | Primary floor search on the smallest supported 4-row trace. |
| `counter4-t128-rate1over4-q60-pow8-arity1` | `counter4` | `128` | `1/4` | `60` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over4-q56-pow16-arity1` | `counter4` | `128` | `1/4` | `56` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over4-q60-pow8-arity2` | `counter4` | `128` | `1/4` | `60` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over4-q56-pow16-arity2` | `counter4` | `128` | `1/4` | `56` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over4-q60-pow8-arity3` | `counter4` | `128` | `1/4` | `60` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over4-q56-pow16-arity3` | `counter4` | `128` | `1/4` | `56` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over8-q40-pow8-arity1` | `counter4` | `128` | `1/8` | `40` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over8-q38-pow16-arity1` | `counter4` | `128` | `1/8` | `38` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over8-q40-pow8-arity2` | `counter4` | `128` | `1/8` | `40` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over8-q38-pow16-arity2` | `counter4` | `128` | `1/8` | `38` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over8-q40-pow8-arity3` | `counter4` | `128` | `1/8` | `40` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over8-q38-pow16-arity3` | `counter4` | `128` | `1/8` | `38` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over16-q30-pow8-arity1` | `counter4` | `128` | `1/16` | `30` | `8` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over16-q28-pow16-arity1` | `counter4` | `128` | `1/16` | `28` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over16-q30-pow8-arity2` | `counter4` | `128` | `1/16` | `30` | `8` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over16-q28-pow16-arity2` | `counter4` | `128` | `1/16` | `28` | `16` | `2` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over16-q30-pow8-arity3` | `counter4` | `128` | `1/16` | `30` | `8` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t128-rate1over16-q28-pow16-arity3` | `counter4` | `128` | `1/16` | `28` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t100-rate1over4-q42-pow16-arity1` | `counter8` | `100` | `1/4` | `42` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t100-rate1over4-q42-pow16-arity3` | `counter8` | `100` | `1/4` | `42` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t100-rate1over16-q21-pow16-arity1` | `counter8` | `100` | `1/16` | `21` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t100-rate1over16-q21-pow16-arity3` | `counter8` | `100` | `1/16` | `21` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t128-rate1over4-q56-pow16-arity1` | `counter8` | `128` | `1/4` | `56` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t128-rate1over4-q56-pow16-arity3` | `counter8` | `128` | `1/4` | `56` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t128-rate1over16-q28-pow16-arity1` | `counter8` | `128` | `1/16` | `28` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter8-t128-rate1over16-q28-pow16-arity3` | `counter8` | `128` | `1/16` | `28` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t100-rate1over4-q42-pow16-arity1` | `counter16` | `100` | `1/4` | `42` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t100-rate1over4-q42-pow16-arity3` | `counter16` | `100` | `1/4` | `42` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t100-rate1over16-q21-pow16-arity1` | `counter16` | `100` | `1/16` | `21` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t100-rate1over16-q21-pow16-arity3` | `counter16` | `100` | `1/16` | `21` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t128-rate1over4-q56-pow16-arity1` | `counter16` | `128` | `1/4` | `56` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t128-rate1over4-q56-pow16-arity3` | `counter16` | `128` | `1/4` | `56` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t128-rate1over16-q28-pow16-arity1` | `counter16` | `128` | `1/16` | `28` | `16` | `1` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter16-t128-rate1over16-q28-pow16-arity3` | `counter16` | `128` | `1/16` | `28` | `16` | `3` | `failed` | `-` | `-` | `-` | panic: assertion failed: target_domain.log_n >= self.domain.log_n |
| `counter4-t100-rate1over2-q84-pow16-arity1-final2` | `counter4` | `100` | `1/2` | `84` | `16` | `1` | `success` | `43149` | `accept` | `accept` | Probe whether log_final_poly_len is actually live on the Circle prover path. |
| `counter4-t100-rate1over2-q84-pow16-arity1-commitpow8` | `counter4` | `100` | `1/2` | `84` | `16` | `1` | `success` | `43149` | `accept` | `accept` | Probe whether commit_proof_of_work_bits changes Circle proofs at all. |

## Divergences

None.
