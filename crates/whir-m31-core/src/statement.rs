use solana_program::hash::hashv;

pub type StatementDigest = [u8; 32];

pub const MAX_NULLIFIERS: usize = 2;
pub const MAX_OUTPUTS: usize = 2;
pub const SPEND_V0_BINDING_BYTES: usize =
    1 + 32 + 1 + (MAX_NULLIFIERS * 32) + 1 + (MAX_OUTPUTS * 32) + 32 + 8;

const SPEND_V0_DOMAIN: &[u8] = b"whir-m31/spend-v0";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpendV0Binding {
    pub anchor: [u8; 32],
    pub nullifier_count: u8,
    pub nullifiers: [[u8; 32]; MAX_NULLIFIERS],
    pub output_count: u8,
    pub outputs: [[u8; 32]; MAX_OUTPUTS],
    pub asset_id: [u8; 32],
    pub fee: u64,
}

impl SpendV0Binding {
    pub fn new(
        anchor: [u8; 32],
        nullifiers: &[[u8; 32]],
        outputs: &[[u8; 32]],
        asset_id: [u8; 32],
        fee: u64,
    ) -> Self {
        assert!(nullifiers.len() <= MAX_NULLIFIERS);
        assert!(outputs.len() <= MAX_OUTPUTS);
        let mut fixed_nullifiers = [[0_u8; 32]; MAX_NULLIFIERS];
        let mut fixed_outputs = [[0_u8; 32]; MAX_OUTPUTS];
        let mut idx = 0;
        while idx < nullifiers.len() {
            fixed_nullifiers[idx] = nullifiers[idx];
            idx += 1;
        }
        idx = 0;
        while idx < outputs.len() {
            fixed_outputs[idx] = outputs[idx];
            idx += 1;
        }
        Self {
            anchor,
            nullifier_count: nullifiers.len() as u8,
            nullifiers: fixed_nullifiers,
            output_count: outputs.len() as u8,
            outputs: fixed_outputs,
            asset_id,
            fee,
        }
    }

    pub fn canonical_bytes(&self) -> [u8; SPEND_V0_BINDING_BYTES] {
        let mut out = [0_u8; SPEND_V0_BINDING_BYTES];
        let mut cursor = 0;
        out[cursor] = 0;
        cursor += 1;
        out[cursor..cursor + 32].copy_from_slice(&self.anchor);
        cursor += 32;
        out[cursor] = self.nullifier_count;
        cursor += 1;
        for value in self.nullifiers {
            out[cursor..cursor + 32].copy_from_slice(&value);
            cursor += 32;
        }
        out[cursor] = self.output_count;
        cursor += 1;
        for value in self.outputs {
            out[cursor..cursor + 32].copy_from_slice(&value);
            cursor += 32;
        }
        out[cursor..cursor + 32].copy_from_slice(&self.asset_id);
        cursor += 32;
        out[cursor..cursor + 8].copy_from_slice(&self.fee.to_le_bytes());
        out
    }

    pub fn from_canonical_bytes(bytes: [u8; SPEND_V0_BINDING_BYTES]) -> Option<Self> {
        if bytes[0] != 0 {
            return None;
        }
        let mut cursor = 1;
        let mut anchor = [0_u8; 32];
        anchor.copy_from_slice(&bytes[cursor..cursor + 32]);
        cursor += 32;
        let nullifier_count = bytes[cursor];
        cursor += 1;
        if nullifier_count as usize > MAX_NULLIFIERS {
            return None;
        }
        let mut nullifiers = [[0_u8; 32]; MAX_NULLIFIERS];
        for slot in &mut nullifiers {
            slot.copy_from_slice(&bytes[cursor..cursor + 32]);
            cursor += 32;
        }
        let output_count = bytes[cursor];
        cursor += 1;
        if output_count as usize > MAX_OUTPUTS {
            return None;
        }
        let mut outputs = [[0_u8; 32]; MAX_OUTPUTS];
        for slot in &mut outputs {
            slot.copy_from_slice(&bytes[cursor..cursor + 32]);
            cursor += 32;
        }
        let mut asset_id = [0_u8; 32];
        asset_id.copy_from_slice(&bytes[cursor..cursor + 32]);
        cursor += 32;
        let mut raw_fee = [0_u8; 8];
        raw_fee.copy_from_slice(&bytes[cursor..cursor + 8]);
        Some(Self {
            anchor,
            nullifier_count,
            nullifiers,
            output_count,
            outputs,
            asset_id,
            fee: u64::from_le_bytes(raw_fee),
        })
    }

    pub fn digest(&self) -> StatementDigest {
        hashv(&[SPEND_V0_DOMAIN, &self.canonical_bytes()]).to_bytes()
    }
}
