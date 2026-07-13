//! Binding/state machine for the named split-verification fallback.
//!
//! This module does not pretend the statement proof exists. It freezes the
//! receipt seam and rejects mix-and-match, reordering, expiry, authority, and
//! replay attacks before the expensive verifiers are connected to it.

use aspis_core::field::QM31;

pub const TERMINAL_POINT_LEN: usize = 10;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptBinding {
    pub session_id: [u8; 32],
    pub authority: [u8; 32],
    pub statement_digest: [u8; 32],
    pub proof_hash: [u8; 32],
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
    pub terminal_point: [QM31; TERMINAL_POINT_LEN],
    pub claimed_evaluations_digest: [u8; 32],
    pub main_claim: QM31,
    pub helper_claim: QM31,
    pub gamma: QM31,
    pub combined_claim: QM31,
}

impl ReceiptBinding {
    pub fn combined_claim_is_consistent(&self) -> bool {
        self.main_claim.add(self.gamma.mul(self.helper_claim)) == self.combined_claim
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptStatus {
    Pending,
    StatementVerified,
    PcsVerified,
    Consumed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptError {
    CombinedClaimMismatch,
    BindingMismatch,
    WrongAuthority,
    Expired,
    VerificationFailed,
    WrongStatus,
    AlreadyConsumed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitVerificationReceipt {
    pub binding: ReceiptBinding,
    pub expires_at_slot: u64,
    pub status: ReceiptStatus,
}

impl SplitVerificationReceipt {
    pub fn new(binding: ReceiptBinding, expires_at_slot: u64) -> Result<Self, ReceiptError> {
        if !binding.combined_claim_is_consistent() {
            return Err(ReceiptError::CombinedClaimMismatch);
        }
        Ok(Self {
            binding,
            expires_at_slot,
            status: ReceiptStatus::Pending,
        })
    }

    fn check_common(
        &self,
        observed: &ReceiptBinding,
        authority: &[u8; 32],
        current_slot: u64,
    ) -> Result<(), ReceiptError> {
        if self.status == ReceiptStatus::Consumed {
            return Err(ReceiptError::AlreadyConsumed);
        }
        if current_slot > self.expires_at_slot {
            return Err(ReceiptError::Expired);
        }
        if authority != &self.binding.authority {
            return Err(ReceiptError::WrongAuthority);
        }
        if observed != &self.binding {
            return Err(ReceiptError::BindingMismatch);
        }
        Ok(())
    }

    /// Called only after the statement-reduction verifier returns. A false
    /// result cannot create a receipt that the PCS transaction can consume.
    pub fn mark_statement_verified(
        &mut self,
        observed: &ReceiptBinding,
        authority: &[u8; 32],
        current_slot: u64,
        verification_succeeded: bool,
    ) -> Result<(), ReceiptError> {
        self.check_common(observed, authority, current_slot)?;
        if self.status != ReceiptStatus::Pending {
            return Err(ReceiptError::WrongStatus);
        }
        if !verification_succeeded {
            return Err(ReceiptError::VerificationFailed);
        }
        self.status = ReceiptStatus::StatementVerified;
        Ok(())
    }

    /// Called only after the wide PCS verifies the exact roots/claim in the
    /// receipt. It cannot run before statement verification.
    pub fn mark_pcs_verified(
        &mut self,
        observed: &ReceiptBinding,
        authority: &[u8; 32],
        current_slot: u64,
        verification_succeeded: bool,
    ) -> Result<(), ReceiptError> {
        self.check_common(observed, authority, current_slot)?;
        if self.status != ReceiptStatus::StatementVerified {
            return Err(ReceiptError::WrongStatus);
        }
        if !verification_succeeded {
            return Err(ReceiptError::VerificationFailed);
        }
        self.status = ReceiptStatus::PcsVerified;
        Ok(())
    }

    /// Pool finalization consumes the receipt exactly once after checking the
    /// nullifier set and applying the output state transition.
    pub fn consume(
        &mut self,
        observed: &ReceiptBinding,
        authority: &[u8; 32],
        current_slot: u64,
    ) -> Result<(), ReceiptError> {
        self.check_common(observed, authority, current_slot)?;
        if self.status != ReceiptStatus::PcsVerified {
            return Err(ReceiptError::WrongStatus);
        }
        self.status = ReceiptStatus::Consumed;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31};

    fn q(value: u32) -> QM31 {
        QM31::from_cm31(CM31::from_m31(M31(value)))
    }

    fn binding(seed: u8) -> ReceiptBinding {
        let main_claim = q(7 + seed as u32);
        let helper_claim = q(11 + seed as u32);
        let gamma = q(13 + seed as u32);
        ReceiptBinding {
            session_id: [seed; 32],
            authority: [seed.wrapping_add(1); 32],
            statement_digest: [seed.wrapping_add(2); 32],
            proof_hash: [seed.wrapping_add(3); 32],
            c1_root: [seed.wrapping_add(4); 32],
            c2_root: [seed.wrapping_add(5); 32],
            terminal_point: core::array::from_fn(|index| q(index as u32 + 17)),
            claimed_evaluations_digest: [seed.wrapping_add(6); 32],
            main_claim,
            helper_claim,
            gamma,
            combined_claim: main_claim.add(gamma.mul(helper_claim)),
        }
    }

    #[test]
    fn canonical_three_transaction_flow_consumes_once() {
        let observed = binding(1);
        let authority = observed.authority;
        let mut receipt = SplitVerificationReceipt::new(observed.clone(), 100).unwrap();
        assert_eq!(
            receipt.mark_statement_verified(&observed, &authority, 10, true),
            Ok(())
        );
        assert_eq!(receipt.status, ReceiptStatus::StatementVerified);
        assert_eq!(
            receipt.mark_pcs_verified(&observed, &authority, 11, true),
            Ok(())
        );
        assert_eq!(receipt.consume(&observed, &authority, 12), Ok(()));
        assert_eq!(
            receipt.consume(&observed, &authority, 13),
            Err(ReceiptError::AlreadyConsumed)
        );
    }

    #[test]
    fn order_failure_and_binding_mix_and_match_reject() {
        let observed = binding(1);
        let authority = observed.authority;
        let mut receipt = SplitVerificationReceipt::new(observed.clone(), 100).unwrap();
        assert_eq!(
            receipt.mark_pcs_verified(&observed, &authority, 10, true),
            Err(ReceiptError::WrongStatus)
        );
        assert_eq!(
            receipt.mark_statement_verified(&binding(2), &authority, 10, true),
            Err(ReceiptError::BindingMismatch)
        );
        assert_eq!(
            receipt.mark_statement_verified(&observed, &authority, 10, false),
            Err(ReceiptError::VerificationFailed)
        );
        assert_eq!(receipt.status, ReceiptStatus::Pending);
    }

    #[test]
    fn authority_expiry_and_combined_claim_attacks_reject() {
        let observed = binding(1);
        let authority = observed.authority;
        let mut receipt = SplitVerificationReceipt::new(observed.clone(), 100).unwrap();
        assert_eq!(
            receipt.mark_statement_verified(&observed, &[99; 32], 10, true),
            Err(ReceiptError::WrongAuthority)
        );
        assert_eq!(
            receipt.mark_statement_verified(&observed, &authority, 101, true),
            Err(ReceiptError::Expired)
        );

        let mut inconsistent = binding(3);
        inconsistent.combined_claim = inconsistent.combined_claim.add(QM31::ONE);
        assert_eq!(
            SplitVerificationReceipt::new(inconsistent, 100),
            Err(ReceiptError::CombinedClaimMismatch)
        );
    }
}
