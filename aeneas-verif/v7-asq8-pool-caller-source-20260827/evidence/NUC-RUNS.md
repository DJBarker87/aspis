# Capped NUC evidence

All heavy jobs ran through `systemd-run --user --scope` with
`MemoryHigh=22G`, `MemoryMax=28G`, and `MemorySwapMax=0`.

- Exact dispatch Charon extraction: exit 0; peak RSS 845,492 KiB; swaps 0.
- Exact dispatch Aeneas translation: exit 0; peak RSS 356,748 KiB; swaps 0.
- Generated dispatch Types/Funs focused Lean: exit 0; peak RSS 2,604,868 KiB
  (largest focused generated run); swaps 0.
- Dispatch source bridge: exit 0; peak RSS 2,561,820 KiB; swaps 0.
- Next-lane generated Types/Funs: all exit 0; peak RSS 2,595,072 KiB; swaps 0.
- Next-lane source bridge: exit 0; peak RSS 2,544,964 KiB; swaps 0.
- Outer write-order bridge: exit 0; peak RSS 2,577,176 KiB; swaps 0.
- Frozen full replay: unit `asq8-caller-full-replay-03`, invocation
  `3da2a3dd54874db29bc18d5f46f42e06`; exit 0; wall 19.33s; peak RSS
  2,606,180 KiB; swaps 0.

The raw outer Aeneas audit exited 2 at source lines 895-1076 with:

> Unimplemented: found an occurrence of a lifetime constraint relating a
> higher-ranked lifetime to a free lifetime.

That diagnostic is retained as an explicit tool limitation; it is not hidden as
a theorem premise.
