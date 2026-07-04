#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum ProfileId {
    WhirM31DevV0 = 1,
    WhirM31SolanaV0 = 2,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum HashMode {
    Sha256 = 1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum WhirFoldMode {
    LocalInterpolant = 1,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SvmRuntimeLimits {
    pub max_compute_units_per_tx: u64,
    pub max_transaction_bytes: u64,
    pub min_heap_frame_bytes: u64,
    pub max_heap_frame_bytes: u64,
    pub heap_page_bytes: u64,
    pub stack_frame_bytes: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WhirProfileManifest {
    pub id: ProfileId,
    pub name: &'static str,
    pub proof_version: u16,
    pub statement_binding_version: u16,
    pub hash_mode: HashMode,
    pub fold_mode: WhirFoldMode,
    pub log_num_rows: u8,
    pub fold_vars_per_round: u8,
    pub query_repetitions_per_round: u8,
    pub query_pow_bits: u8,
    pub target_security_bits: u16,
    pub heap_frame_bytes: u32,
    pub upload_chunk_bytes: u16,
    pub runtime_limits: SvmRuntimeLimits,
}

pub const TRANSCRIPT_DOMAIN: &[u8] = b"whir-m31/transcript/v0";
pub const TRANSCRIPT_ROOT_LABEL: &[u8] = b"whir-m31/root";
pub const TRANSCRIPT_ROUND_X_LABEL: &[u8] = b"whir-m31/round-x";
pub const TRANSCRIPT_ROUND_Y_LABEL: &[u8] = b"whir-m31/round-y";
pub const TRANSCRIPT_FINAL_VALUE_LABEL: &[u8] = b"whir-m31/final-value";
pub const TRANSCRIPT_QUERY_LABEL: &[u8] = b"whir-m31/query";

pub const COMMON_LIMITS: SvmRuntimeLimits = SvmRuntimeLimits {
    max_compute_units_per_tx: 1_400_000,
    max_transaction_bytes: 1_232,
    min_heap_frame_bytes: 32_768,
    max_heap_frame_bytes: 262_144,
    heap_page_bytes: 32_768,
    stack_frame_bytes: 4_096,
};

pub const WHIR_M31_DEV_V0: WhirProfileManifest = WhirProfileManifest {
    id: ProfileId::WhirM31DevV0,
    name: "whir-m31-dev-v0",
    proof_version: 0,
    statement_binding_version: 0,
    hash_mode: HashMode::Sha256,
    fold_mode: WhirFoldMode::LocalInterpolant,
    log_num_rows: 8,
    fold_vars_per_round: 2,
    query_repetitions_per_round: 4,
    query_pow_bits: 0,
    target_security_bits: 96,
    heap_frame_bytes: 32 * 1024,
    upload_chunk_bytes: 640,
    runtime_limits: COMMON_LIMITS,
};

pub const WHIR_M31_SOLANA_V0: WhirProfileManifest = WhirProfileManifest {
    id: ProfileId::WhirM31SolanaV0,
    name: "whir-m31-solana-v0",
    proof_version: 0,
    statement_binding_version: 0,
    hash_mode: HashMode::Sha256,
    fold_mode: WhirFoldMode::LocalInterpolant,
    log_num_rows: 12,
    fold_vars_per_round: 2,
    query_repetitions_per_round: 8,
    query_pow_bits: 0,
    target_security_bits: 128,
    heap_frame_bytes: 64 * 1024,
    upload_chunk_bytes: 640,
    runtime_limits: COMMON_LIMITS,
};

pub fn profile_manifest(id: ProfileId) -> &'static WhirProfileManifest {
    match id {
        ProfileId::WhirM31DevV0 => &WHIR_M31_DEV_V0,
        ProfileId::WhirM31SolanaV0 => &WHIR_M31_SOLANA_V0,
    }
}

impl WhirProfileManifest {
    pub const fn round_count(&self) -> usize {
        (self.log_num_rows as usize) / (self.fold_vars_per_round as usize)
    }

    pub const fn block_count_at_round(&self, round: usize) -> usize {
        1 << (self.log_num_rows as usize - self.fold_vars_per_round as usize * (round + 1))
    }

    pub const fn current_block_bytes(&self, round: usize) -> usize {
        if round == 0 {
            16
        } else {
            64
        }
    }

    pub const fn next_block_bytes(&self, round: usize) -> usize {
        if round + 1 < self.round_count() {
            64
        } else {
            0
        }
    }

    pub const fn current_merkle_depth(&self, round: usize) -> usize {
        self.log_num_rows as usize - self.fold_vars_per_round as usize * (round + 1)
    }

    pub const fn next_merkle_depth(&self, round: usize) -> usize {
        if round + 1 < self.round_count() {
            self.log_num_rows as usize - self.fold_vars_per_round as usize * (round + 2)
        } else {
            0
        }
    }

    pub const fn round_query_bytes(&self, round: usize) -> usize {
        self.current_block_bytes(round)
            + (self.current_merkle_depth(round) * 32)
            + self.next_block_bytes(round)
            + (self.next_merkle_depth(round) * 32)
    }
}
