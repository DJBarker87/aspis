use crate::field::{Qm31, M31};
use crate::profile::{
    ProfileId, TRANSCRIPT_DOMAIN, TRANSCRIPT_FINAL_VALUE_LABEL, TRANSCRIPT_QUERY_LABEL,
    TRANSCRIPT_ROOT_LABEL, TRANSCRIPT_ROUND_X_LABEL, TRANSCRIPT_ROUND_Y_LABEL,
};
use crate::statement::StatementDigest;
use solana_program::hash::hashv;

pub struct Transcript {
    state: [u8; 32],
    sample_counter: u64,
}

impl Transcript {
    pub fn new(profile_id: ProfileId, statement_digest: &StatementDigest) -> Self {
        Self {
            state: hashv(&[
                TRANSCRIPT_DOMAIN,
                &(profile_id as u16).to_le_bytes(),
                statement_digest,
            ])
            .to_bytes(),
            sample_counter: 0,
        }
    }

    pub fn absorb_root(&mut self, round: usize, root: &[u8; 32]) {
        self.absorb(TRANSCRIPT_ROOT_LABEL, &(round as u16).to_le_bytes(), root);
    }

    pub fn absorb_final_value(&mut self, bytes: &[u8]) {
        self.absorb(
            TRANSCRIPT_FINAL_VALUE_LABEL,
            &self.sample_counter.to_le_bytes(),
            bytes,
        );
    }

    pub fn sample_round_challenge_pair(&mut self, round: usize) -> (Qm31, Qm31) {
        let x = self.sample_qm31(TRANSCRIPT_ROUND_X_LABEL, round, 0);
        let y = self.sample_qm31(TRANSCRIPT_ROUND_Y_LABEL, round, 1);
        (x, y)
    }

    pub fn sample_query_index(&mut self, round: usize, repetition: usize, domain: usize) -> usize {
        let digest = self.sample_digest(TRANSCRIPT_QUERY_LABEL, round, repetition);
        let mut raw = [0_u8; 8];
        raw.copy_from_slice(&digest[..8]);
        (u64::from_le_bytes(raw) as usize) % domain.max(1)
    }

    fn sample_qm31(&mut self, label: &[u8], round: usize, lane: usize) -> Qm31 {
        let digest = self.sample_digest(label, round, lane);
        let mut limbs = [M31::ZERO; 4];
        let mut index = 0;
        while index < 4 {
            let start = index * 4;
            let mut raw = [0_u8; 4];
            raw.copy_from_slice(&digest[start..start + 4]);
            limbs[index] = M31::from(u32::from_le_bytes(raw));
            index += 1;
        }
        Qm31::from_m31_array(limbs)
    }

    fn absorb(&mut self, label: &[u8], context: &[u8], bytes: &[u8]) {
        self.state = hashv(&[&self.state, label, context, bytes]).to_bytes();
    }

    fn sample_digest(&mut self, label: &[u8], round: usize, repetition: usize) -> [u8; 32] {
        let digest = hashv(&[
            &self.state,
            label,
            &(round as u16).to_le_bytes(),
            &(repetition as u16).to_le_bytes(),
            &self.sample_counter.to_le_bytes(),
        ])
        .to_bytes();
        self.state = hashv(&[&self.state, label, &digest]).to_bytes();
        self.sample_counter = self.sample_counter.wrapping_add(1);
        digest
    }
}
