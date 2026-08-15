import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V5RowAccess.Types

/-!
The filtered extraction leaves an unused external declaration for the other
private `row` method on `AtomicSelectors`.  The retained generated definitions
do not reference it. This module is intentionally empty rather than declaring
anything for unreachable code.
-/
