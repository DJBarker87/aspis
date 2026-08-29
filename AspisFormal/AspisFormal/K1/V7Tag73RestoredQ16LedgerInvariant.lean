import AspisFormal.K1.V7Tag73RestoredDerivedK13View
import AspisFormal.K1.V7Tag73Q16LedgerCertificate

/-!
# Restoration-stable q16 ledger certificates

The future-free verifier deliberately discards the old transition list when
it restores a fork.  It does not discard the selected q16 candidate ledger:
that ledger is part of the restored snapshot.  This file isolates the exact
certificate carried by that snapshot and constructs it directly at the
compact-candidate transition.

No parser field, acceptance predicate, probability bound, or extraction
conclusion appears in this layer.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RestoredQ16LedgerInvariant

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73Q16LedgerCertificate

noncomputable section

/-- Restoring to a transition's before-snapshot retains the selected ledger
exactly.  Unlike the transition list, no historical q16 certificate is lost. -/
def restore_indexed_transition_preserves_selected_q16_ledger
    (environment : FutureFreeEnvironment)
    (transition : FutureFreeTransition)
    (certificate : SelectedQ16LedgerCertificate environment transition.before) :
    SelectedQ16LedgerCertificate environment
      (restoreIndexedTransition transition).current := by
  exact certificate

/-- Package a restoration-stable q16 certificate with the independent fixed
field and challenge-decoding evidence to obtain the corrected K1.3 input. -/
def restored_operational_k13_data_of_selected_ledger
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {node : RestoredK13Node Statement Payload}
    (decoded : Fin 641 → AspisV5ComponentCQM31TowerExact.QM31Exact)
    (fixedDecode : AspisK1.V7Tag73FixedFieldMessageBridge.FixedFieldDecodeExact
      node.adversaryValue.rawMessages decoded)
    (gamma : AspisV5ComponentCQM31TowerExact.QM31Exact)
    (gammaBytes : Qm31Bytes)
    (gammaRecorded :
      { id := ChallengeId.gamma, value := gammaBytes } ∈
        node.verifierFinalState.current.decodedChallenges)
    (gammaDecoded :
      AspisK1.V7Tag73SecureCircleMap.decodeTagQM31ExactLE gammaBytes =
        some gamma)
    (alphaZero : AspisV5ComponentCQM31TowerExact.QM31Exact)
    (alphaZeroBytes : Qm31Bytes)
    (alphaZeroRecorded :
      { id := ChallengeId.alpha 0, value := alphaZeroBytes } ∈
        node.verifierFinalState.current.decodedChallenges)
    (alphaZeroDecoded :
      AspisK1.V7Tag73SecureCircleMap.decodeTagQM31ExactLE alphaZeroBytes =
        some alphaZero)
    (q16 : SelectedQ16LedgerCertificate environment
      node.verifierFinalState.current) :
    RestoredOperationalK13Data environment node :=
  { decoded := decoded
    fixedDecode := fixedDecode
    gamma := gamma
    gammaBytes := gammaBytes
    gammaRecorded := gammaRecorded
    gammaDecoded := gammaDecoded
    alphaZero := alphaZero
    alphaZeroBytes := alphaZeroBytes
    alphaZeroRecorded := alphaZeroRecorded
    alphaZeroDecoded := alphaZeroDecoded
    priorCandidates := q16.priorCandidates
    selectedCounter := q16.selectedCounter
    selectedSchedule := q16.selectedSchedule
    priorHistory := q16.priorHistory
    selectedCompact := q16.selectedCompact
    candidateLedgerExact := q16.ledgerExact }

#print axioms restore_indexed_transition_preserves_selected_q16_ledger
#print axioms restored_operational_k13_data_of_selected_ledger

end

end AspisK1.V7Tag73RestoredQ16LedgerInvariant
