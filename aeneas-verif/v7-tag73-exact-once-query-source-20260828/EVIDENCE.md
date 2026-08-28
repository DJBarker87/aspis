# Reproduction evidence

Every recorded NUC run used a task-owned `systemd-run --user --scope` unit,
`MemorySwapMax=0`, and exited successfully.  Peak RSS is `/usr/bin/time -v`
maximum resident set size.

| Unit | Target | Exit | Wall | Peak RSS | Swap |
|---|---|---:|---:|---:|---:|
| `aspis-v7-exact-once-full-replay03.scope` | source/LLBC/normalization hash checks + all generated modules/proofs + project leaf | 0 | 15.02 s | 6,217,280 KB | 0 |
| `aspis-v7-exact-once-lean-leaf09.scope` | final project exact-once leaf | 0 | 2.99 s | 6,219,400 KB | 0 |
| `aspis-v7-exact-once-parser-proof11.scope` | generated parser source proof | 0 | 3.22 s | 2,535,948 KB | 0 |
| `aspis-v7-exact-once-consumer-generated02.scope` | generated normalized consumer | 0 | 1.97 s | 2,576,808 KB | 0 |
| `aspis-v7-exact-once-consumer-proof05.scope` | generated consumer source proof | 0 | 1.70 s | 2,563,376 KB | 0 |

Successful extraction runs (all swap zero) were:

- direct selected consumer Charon: 3.00 s, 834,676 KB; Aeneas: 1.78 s,
  259,908 KB;
- transparent selected packed decoder Charon: 2.66 s, 840,632 KB; Aeneas:
  1.39 s, 227,628 KB;
- normalized validation consumer Charon: 3.00 s, 833,912 KB; Aeneas:
  1.64 s, 317,836 KB;
- production parser wrapper Charon: 3.15 s, 663,828 KB; Aeneas: 0.89 s,
  191,420 KB.

Pinned source revision:
`8178d3de1d24d7a3a0102739cb63aca8d7a125a8`.

Final `#print axioms` output is summarized in `AXIOMS.md` and emitted directly
by each proof file during replay.
