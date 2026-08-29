# Terminal return-capture compatibility fix

After conditional drop cleanup was recognized, a focused statement trace
showed a genuine loop-state correlation loss.  One exit wrote Rust return local
zero, moved it into `pending_return`, and broke.  The loop fixed point then
generalized `pending_return` while local zero was bottom; its symbolic `None`
branch reached the canonical return suffix and attempted to move local zero a
second time.

Using a synthetic `Copy` would conceal the problem and would be invalid for
non-`Copy` Rust return types.  This patch instead preserves the production move
chain.  A whole-local-zero `Assign` or `Call` that is immediately followed by
only certified drop/lifetime cleanup and `Break`/`Return` is retargeted to one
fresh same-typed capture local.  The capture is moved exactly once into the
existing pending-return option before the path breaks.  No intermediate return
write or projection write matches this rule, and call unwind behavior is
retained.

Drop-specific certificate cases are active only in Aeneas's default
`drop_as_no_op` mode. They accept lifetime no-ops, explicit drops, Boolean drop
flags, and the already-audited conditional-drop forms. The only independent
case is an exact one-arm-plus-otherwise `Match` whose two blocks are literally
empty: a rustc cleanup discriminant with no semantic action. Any other
statement stops the certificate. Explicit-drop translation remains unchanged
under `-eval-drops`.
