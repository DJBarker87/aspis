use winterfell::{
    crypto::{hashers::Sha2_256, DefaultRandomCoin, MerkleTree},
    math::{fields::f128::BaseElement, FieldElement, ToElements},
    verify as stark_verify, AcceptableOptions, Air, AirContext, Assertion, EvaluationFrame, Proof,
    ProofOptions, TraceInfo, TransitionConstraintDegree, VerifierError,
};

type H = Sha2_256<BaseElement>;
type VC = MerkleTree<H>;
type RC = DefaultRandomCoin<H>;

#[derive(Clone, Copy)]
pub struct RealFriVerifyOutcome {
    pub digest: u32,
}

#[derive(Clone, Copy)]
pub struct RealFriPublicInputs {
    pub seed: BaseElement,
    pub inc: BaseElement,
}

impl ToElements<BaseElement> for RealFriPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.seed, self.inc]
    }
}

pub struct RealFriAir {
    ctx: AirContext<BaseElement>,
    pi: RealFriPublicInputs,
}

impl RealFriAir {
    fn new(info: TraceInfo, pi: RealFriPublicInputs, opts: ProofOptions) -> Self {
        let degrees = vec![TransitionConstraintDegree::new(1)];
        let ctx = AirContext::new(info, degrees, 2, opts);
        Self { ctx, pi }
    }
}

impl Air for RealFriAir {
    type BaseField = BaseElement;
    type PublicInputs = RealFriPublicInputs;

    fn new(info: TraceInfo, pi: RealFriPublicInputs, opts: ProofOptions) -> Self {
        Self::new(info, pi, opts)
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.ctx
    }

    fn evaluate_transition<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic: &[E],
        result: &mut [E],
    ) {
        let inc = E::from(self.pi.inc);
        result[0] = frame.next()[0] - frame.current()[0] - inc;
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last = self.trace_length() - 1;
        vec![
            Assertion::single(0, 0, self.pi.seed),
            Assertion::single(
                0,
                last,
                self.pi.seed + (self.pi.inc * BaseElement::from(last as u64)),
            ),
        ]
    }
}

pub fn run_real_fri_verify(
    proof_bytes: &[u8],
    seed_u64: u64,
    inc_u64: u64,
    repeat: u32,
) -> Result<RealFriVerifyOutcome, &'static str> {
    let acceptable = AcceptableOptions::MinConjecturedSecurity(127);
    let public_inputs = RealFriPublicInputs {
        seed: BaseElement::from(seed_u64),
        inc: BaseElement::from(inc_u64),
    };

    let mut digest = 0_u32;
    for round in 0..repeat.max(1) {
        let proof = Proof::from_bytes(proof_bytes).map_err(|_| "winterfell proof parse failed")?;
        stark_verify::<RealFriAir, H, RC, VC>(proof, public_inputs, &acceptable)
            .map_err(map_verifier_error)?;
        let round_tag = [
            (seed_u64 as u32).rotate_left(round % 31),
            ((seed_u64 >> 32) as u32).rotate_left((round + 7) % 31),
            (inc_u64 as u32).rotate_left((round + 13) % 31),
            ((inc_u64 >> 32) as u32).rotate_left((round + 19) % 31),
        ];
        digest ^= round_tag[0] ^ round_tag[1] ^ round_tag[2] ^ round_tag[3];
    }

    Ok(RealFriVerifyOutcome { digest })
}

fn map_verifier_error(_err: VerifierError) -> &'static str {
    "winterfell verification failed"
}
