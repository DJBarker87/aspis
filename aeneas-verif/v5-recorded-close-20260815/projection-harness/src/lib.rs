#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CloseError {
    InvalidOwner,
    MissingSignature,
    NotWritable,
    SameAddress,
    InvalidProof,
    ZeroBalance,
    Overflow,
    ShortData,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CloseChecks {
    pub uploaded_bounds_valid: bool,
    pub proof_finalized: bool,
    pub proof_owned_by_program: bool,
    pub proof_signer: bool,
    pub refund_signer: bool,
    pub proof_writable: bool,
    pub refund_writable: bool,
    pub distinct_addresses: bool,
    pub refund_system_owned: bool,
    pub data_has_four_bytes: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CloseState<S> {
    pub proof_prefix: [u8; 4],
    pub proof_suffix: S,
    pub proof_lamports: u64,
    pub refund_lamports: u64,
}

pub fn source_shaped_close<S>(
    checks: CloseChecks,
    state: CloseState<S>,
) -> Result<CloseState<S>, CloseError> {
    if !checks.uploaded_bounds_valid || !checks.proof_finalized {
        return Err(CloseError::InvalidProof);
    }
    if !checks.proof_owned_by_program {
        return Err(CloseError::InvalidOwner);
    }
    if !checks.proof_signer || !checks.refund_signer {
        return Err(CloseError::MissingSignature);
    }
    if !checks.proof_writable || !checks.refund_writable {
        return Err(CloseError::NotWritable);
    }
    if !checks.distinct_addresses {
        return Err(CloseError::SameAddress);
    }
    if !checks.refund_system_owned {
        return Err(CloseError::InvalidOwner);
    }
    if state.proof_lamports == 0 {
        return Err(CloseError::ZeroBalance);
    }
    let refunded_balance = match state
        .refund_lamports
        .checked_add(state.proof_lamports)
    {
        Some(value) => value,
        None => return Err(CloseError::Overflow),
    };
    if !checks.data_has_four_bytes {
        return Err(CloseError::ShortData);
    }
    Ok(CloseState {
        proof_prefix: [65, 83, 80, 67],
        proof_suffix: state.proof_suffix,
        proof_lamports: 0,
        refund_lamports: refunded_balance,
    })
}
