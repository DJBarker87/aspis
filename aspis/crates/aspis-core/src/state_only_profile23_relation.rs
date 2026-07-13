//! Fused relation preparation for profile 23's appended zero-factor D lane.

use crate::field::QM31;
use crate::state_only_prefix::STATE_ONLY_PROFILE23_D_CLAIMS_LEN;
use crate::state_only_profile23_query::{
    StateOnlyProfile23QueryPowers, PROFILE23_D_GENERATOR_INDEX,
};
use crate::state_only_relation::{prepare_state_only_relation, StateOnlyRelationPrepared};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StateOnlyProfile23RelationPrepared {
    /// Ordinary relation object with its three claims extended by gamma^28 D.
    /// The embedded base query powers remain the exact width-28 prefix.
    pub relation: StateOnlyRelationPrepared,
    pub query_powers: StateOnlyProfile23QueryPowers,
    pub d_claims: [QM31; 3],
}

pub fn prepare_state_only_profile23_relation(
    gamma: QM31,
    base_statement_bytes: &[u8],
    d_claims_bytes: &[u8; STATE_ONLY_PROFILE23_D_CLAIMS_LEN],
) -> Option<StateOnlyProfile23RelationPrepared> {
    let mut relation = prepare_state_only_relation(gamma, base_statement_bytes)?;
    let d_claims: [QM31; 3] = core::array::from_fn(|point| {
        let start = point * 16;
        QM31::from_le_bytes(&d_claims_bytes[start..start + 16]).unwrap_or(QM31::ZERO)
    });
    for point in 0..3 {
        let start = point * 16;
        if QM31::from_le_bytes(&d_claims_bytes[start..start + 16]).is_none() {
            return None;
        }
    }
    let d_power = gamma.pow(PROFILE23_D_GENERATOR_INDEX as u64);
    for point in 0..3 {
        relation.claims[point] = relation.claims[point].add(d_power.mul(d_claims[point]));
    }
    Some(StateOnlyProfile23RelationPrepared {
        query_powers: StateOnlyProfile23QueryPowers::from_base_and_d(
            relation.query_powers,
            d_power,
        ),
        relation,
        d_claims,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{CM31, M31};
    use crate::state_only_relation::STATE_ONLY_STATEMENT_BYTES;

    #[test]
    fn d_claims_are_exactly_gamma_28_and_canonical() {
        let gamma = QM31::from_cm31(CM31::from_m31(M31(7)));
        let base = [0u8; STATE_ONLY_STATEMENT_BYTES];
        let claims = [
            QM31::from_cm31(CM31::from_m31(M31(3))),
            QM31::from_cm31(CM31::from_m31(M31(5))),
            QM31::from_cm31(CM31::from_m31(M31(11))),
        ];
        let mut bytes = [0u8; STATE_ONLY_PROFILE23_D_CLAIMS_LEN];
        for (point, value) in claims.iter().enumerate() {
            value.write_le_bytes(&mut bytes[point * 16..][..16]);
        }
        let prepared = prepare_state_only_profile23_relation(gamma, &base, &bytes).unwrap();
        let power = gamma.pow(28);
        assert_eq!(
            prepared.relation.claims,
            claims.map(|value| power.mul(value))
        );
        bytes[0..4].copy_from_slice(&crate::field::P.to_le_bytes());
        assert!(prepare_state_only_profile23_relation(gamma, &base, &bytes).is_none());
    }
}
