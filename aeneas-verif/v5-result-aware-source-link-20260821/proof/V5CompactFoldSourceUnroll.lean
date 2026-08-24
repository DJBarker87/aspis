import V5CompactFoldTenBlockSemantics

/-!
Aggregate import for the exact compact-fold source equality at all four
counter values reachable in the released verifier.  The shared iterator
induction avoids retaining four separately unrolled mutable-loop terms.
-/
