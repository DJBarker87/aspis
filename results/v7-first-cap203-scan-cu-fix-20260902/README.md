# V7 first-cap-203 final-nonce cutoff measurement

The default-off audit prover selected an ordinary genuine Tag-73 proof at
counter 9 under an inclusive cutoff of 20. The unchanged verifier accepted it
in a finalized disposable Agave 4.2.0 withdrawal transaction: 1,543 bytes and
1,196,956 CU in both simulation and landed execution.

The current-binary withdrawal-rollover counter-0 baseline is 1,218,972 CU at
frontier 202. The calibrated maximum-frontier envelope puts cutoff 20 at
1,299,084 CU, cutoff 27 at 1,326,965 CU, and cutoff 32 at 1,346,880 CU.
These are calibrated measurements, not an all-reachable-transcript theorem.

Classification: **MEASUREMENT GREEN; RELEASE PROMOTION BLOCKED BY FINAL-NONCE
FORMAL BRIDGE**. `mainnetReady` remains `false`.
