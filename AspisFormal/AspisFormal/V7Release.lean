import AspisFormal.V6AcceptedPathObligations
import AspisFormal.V6HidingFinalFactorization
import AspisFormal.V6PairedSaltHiding
import AspisFormal.V7SplitTensorProfile
import AspisFormal.V7BooleanZeta
import AspisFormal.V7GammaRestriction
import AspisFormal.V7PublishedCodeSwitchInterfaces
import AspisFormal.V7CompactOneFold
import AspisFormal.V7AuthenticatedWire
import AspisFormal.V7CompactFrontierDeltaCertificate
import AspisFormal.V7CompactFrontierCertificate
import AspisFormal.V7CompactSecurityLedger
import AspisFormal.V7ConditionalCompleteSecurity

/-!
# Focused V7 formal release closure

This import-only module is the focused build target for the selected V7
one-fold release.  It includes the split-tensor algebra and exact deployed
QM31 restriction, the exact cap-203 recurrence and security arithmetic, the
reused V6 accepted-path/final-factorization/paired-salt results, and the V7
complete-C2/208-bit wire specialization.

Import closure is not theorem composition: the numerical capstone proves a
conditional false-acceptance bound only.  Its external coding, event,
Fiat--Shamir, primitive, and source-correspondence interfaces remain premises;
the separate hiding modules do not turn that result into unconditional HVZK or
theft resistance.
-/
