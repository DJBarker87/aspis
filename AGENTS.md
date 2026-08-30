# Aspis build and formal-proof operating rules

These rules apply to every agent and human-driven automation in this
repository.  They exist because several large Lean replays consumed tens of
gigabytes while trying to normalize concrete recurrence terms that reduced to
small symbolic facts.

## Formal proof workflow

1. Compile the smallest changed `.lean` file first with `lake env lean`.
   Do not start a package-wide or manifest replay to discover a local theorem
   error.
2. Before evaluating a large generated numeral or recurrence cell, inspect its
   mathematical shape.  Prove and use sparsity, zero, monotonicity, symmetry,
   or closed-form lemmas first.  Kernel reduction of a huge term is a last
   resort, not the default proof method.
3. Generators must identify exceptional/sparse cells explicitly and emit a
   named symbolic theorem application for them.  Do not emit `rfl`, broad
   `simp`, `norm_num`, or an unfolded recurrence for a cell whose reduction
   graph is large.
4. Test a new generic lemma directly, then one affected generated chunk, then
   the bridge theorem.  Run the complete frozen manifest only once after those
   focused targets are green.
5. Do not repeat an unchanged full regression.  A rerun needs a source change,
   toolchain/environment change, missing evidence artifact, or a specifically
   identified nondeterminism question.
6. Every formal release result must record the exact target, exit status, wall
   time, peak RSS, swap, source revision, and `#print axioms` result.

## Resource policy

1. Use an ordinary development machine for source inspection, editing, and
   focused jobs expected to remain below 8 GiB. Send generated-certificate
   aggregation, Aeneas replay, SBF rebuilds, and other RAM-intensive work to a
   dedicated Linux build host.
   A cold Lean dependency build is not a focused local job: monitor aggregate
   child-process RSS and stop or move it to the build host as soon as it approaches
   8 GiB rather than waiting for the parent process to report completion.
2. Every large build must run in its own systemd/cgroup scope with
   `MemorySwapMax=0`.  Set explicit `MemoryHigh` and `MemoryMax`; never run an
   uncapped Lean, Aeneas, Rust, or linker job.
3. Keep the sum of simultaneous `MemoryMax` values below the host's safe
   working limit. Reserve enough memory for the OS and remote control path.
4. Crossing 24 GiB RSS, or spending ten minutes without a new compiled target,
   is a mandatory review point.  Stop or pause before raising the cap unless a
   focused predecessor already proved that the remaining work is legitimate
   final aggregation rather than pathological reduction.
5. A job killed by memory pressure must not be rerun unchanged with a larger
   cap.  First isolate the declaration/cell, inspect its reduction shape, and
   change the proof or generator.  Record the old failure and the replacement.
6. Reuse a pinned build workspace and compiled cache between focused dependent
   targets.  Do not rebuild thousands of unchanged modules merely to test the
   next bridge.
7. Execute dense finite-field elimination, rank probes, large proof generation,
   and other arithmetic release gates with an optimized Rust binary
   (`cargo test --release` or an explicitly optimized profile). A debug build
   may be used for type-checking or a tiny preflight only; it must not become
   the long-running build-host job.
8. Before launching a heavy Rust gate, record whether time is expected in
   compilation, proof generation, or one named aggregation/elimination step.
   If an unoptimized process is discovered doing the heavy step, stop it and
   replace it with the optimized, identically scoped command instead of waiting
   for sunk time to justify more sunk time.

## Generated-certificate preflight

Before starting a full certificate build:

- run the generator's `--check` or equivalent manifest validation;
- compile every changed generic recurrence lemma;
- compile each exceptional generated chunk independently;
- search changed chunks for broad unfolding or large `norm_num`/`decide`
  proofs;
- confirm the cgroup cap and current aggregate build-host reservation;
- identify the exact next theorem that consumes the certificate.

If a concrete cell becomes fast only after a symbolic lemma, add that cell
shape to the generator so the optimization is permanent.

## Verification cadence

The normal cadence is: focused proof, dependent bridge, one axioms audit, one
final manifest replay.  Adversarial/runtime/reproducible-build suites are run
when their covered source or artifact changes, not after every unrelated Lean
edit.
