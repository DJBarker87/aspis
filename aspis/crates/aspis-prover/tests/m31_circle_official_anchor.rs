use aspis_core::field::{CM31, M31, P, QM31};
use aspis_prover::circle_candidate::{
    c1_layer0_leaves, c1_layer0_root, c2_layer0_leaves, c2_layer0_root, CircleEncoder, C1_COLUMNS,
    C2_COLUMNS, CODEWORD_LEN, TRACE_LEN,
};
use aspis_prover::HOST_HASH;
use sha2::{Digest as _, Sha256};

const C1_CODEWORDS: &str = "eb398b5bf27587d3d4abb693287530dc8aacc4f8ed0470b3e9133d331d2694ea";
const C2_CODEWORDS: &str = "7badaace498a8a1837b9f018dffe193ba1cb3528646578439391aecffbcc34a2";
const C1_LEAVES: &str = "2f0dc5ce5f7bdc604e544bc01c9d42b8d24bc8caf15625bd6e2336324c4adb69";
const C2_LEAVES: &str = "1be451ce4ff8a8a7ece496eb6ec05ead3de4645238d02c35a5b75ca1050c90c5";
const C1_ROOT: &str = "c6a93117eb8ccd3e0e9c3ff9598ce6f34682f82c430a955da1c0f799c6c2ad4f";
const C2_ROOT: &str = "c764cdff2474ee79b56fe9baeaa3c7cc5e62c2ae3b1f0ed470c00c28f83930b3";
const FIXTURE: &str = "a130a5cb2bb8055423d5db9bc0ebbf563ef00e651efd6ee989816178bdc3c671";

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    fn m31(&mut self) -> M31 {
        M31((self.next() as u32) % P)
    }

    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

fn fixture() -> (Vec<Vec<M31>>, Vec<Vec<QM31>>) {
    let mut rng = Rng(0x4349_5243_4c45_4332);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| rng.m31().add(M31((column * 65_537 + row * 257 + 1) as u32)))
                .collect()
        })
        .collect();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut value = rng.qm31();
                    value.c0.a = value.c0.a.add(M31((helper * 4099 + row + 1) as u32));
                    value
                })
                .collect()
        })
        .collect();
    (c1, c2)
}

fn digest_c1(codewords: &[Vec<M31>]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for codeword in codewords {
        for value in codeword {
            hasher.update(value.to_le_bytes());
        }
    }
    hasher.finalize().into()
}

fn digest_c2(codewords: &[Vec<QM31>]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    let mut bytes = [0u8; 16];
    for codeword in codewords {
        for value in codeword {
            value.write_le_bytes(&mut bytes);
            hasher.update(bytes);
        }
    }
    hasher.finalize().into()
}

fn digest_leaves<const N: usize>(leaves: &[[u8; N]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for leaf in leaves {
        hasher.update(leaf);
    }
    hasher.finalize().into()
}

fn hex(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
fn candidate_encoder_matches_retained_official_stwo_full_digest_anchor() {
    let (c1_messages, c2_messages) = fixture();
    let encoder = CircleEncoder::new();
    let c1 = encoder.encode_c1_columns(&c1_messages).unwrap();
    let c2 = encoder.encode_c2_columns(&c2_messages).unwrap();
    assert_eq!(c1.len(), C1_COLUMNS);
    assert_eq!(c2.len(), C2_COLUMNS);
    assert!(c1.iter().all(|codeword| codeword.len() == CODEWORD_LEN));
    assert!(c2.iter().all(|codeword| codeword.len() == CODEWORD_LEN));

    let c1_leaves = c1_layer0_leaves(&c1).unwrap();
    let c2_leaves = c2_layer0_leaves(&c2).unwrap();
    let values = [
        digest_c1(&c1),
        digest_c2(&c2),
        digest_leaves(&c1_leaves),
        digest_leaves(&c2_leaves),
        c1_layer0_root(&c1, HOST_HASH).unwrap(),
        c2_layer0_root(&c2, HOST_HASH).unwrap(),
    ];
    assert_eq!(hex(values[0]), C1_CODEWORDS);
    assert_eq!(hex(values[1]), C2_CODEWORDS);
    assert_eq!(hex(values[2]), C1_LEAVES);
    assert_eq!(hex(values[3]), C2_LEAVES);
    assert_eq!(hex(values[4]), C1_ROOT);
    assert_eq!(hex(values[5]), C2_ROOT);

    let mut anchor = b"aspis:official-stwo-circle-candidate-digests:v1".to_vec();
    for value in values {
        anchor.extend_from_slice(&value);
    }
    assert_eq!(hex(Sha256::digest(anchor).into()), FIXTURE);
}
