# Focused replay result

Status: **CHARON AND PURE LAYOUT GREEN; AENEAS FIX READY, WAITING FOR MEMORY**

The production revision, 115-file source closure, accepted call graph, and
39-MiB LLBC are frozen. Charon completed successfully; the LLBC SHA-256 is
`d05f26ee7b8bbd4f16c3bccd50348b129d1c25dd51a950730141a9e418d479e3`.
The focused pure layout model passed on the NUC in 4.63 seconds with peak RSS
6,727,628 KiB, zero swaps, no OOM, and exit status zero.

The original Aeneas run was stopped after it proved pathological. Focused
traces reduced the remaining failure to rustc's terminal-return cleanup around
`finish_onefold_relation`, not production Rust. Nine preceding compatibility
patches advanced translation through every earlier failure. The tenth patch,
`aeneas-d860ac47-terminal-return-capture.patch`, preserves Rust move semantics:
it retargets only certified terminal local-zero producers to a fresh capture,
moves the capture once into the existing pending-return option, and recognizes
only audited no-op cleanup shapes. It never synthesizes `Copy` for the
non-`Copy` production return value. Applying all ten patches produces Aeneas
Git tree `de8340302a8a14448e47e2a878ac726ed29228b2`.

The required replay has not been launched below the memory gate. At the latest
check, `MemAvailable` was 15,419,340 KiB because an active Aspis Q16 lane had
many 7--8-GiB Lean workers. This is below the mandatory 24-GiB threshold, so no
competing Aeneas build was started. The next safe operation is the isolated
translator build and production replay under `MemoryHigh=18G`,
`MemoryMax=20G`, and `MemorySwapMax=0`.

Exact final commands, wall time, peak RSS, swap/OOM status, generated hashes,
strongest theorem names, and complete axiom output will be appended after that
safe focused replay.
