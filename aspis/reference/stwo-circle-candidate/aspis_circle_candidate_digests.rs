use stwo::core::fields::m31::{M31, P};
use stwo::core::fields::qm31::SecureField;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::cpu::CpuCirclePoly;

const TRACE_LEN: usize = 1 << 10;
const CODEWORD_LEN: usize = 1 << 12;
const FIBER_COUNT: usize = 1 << 10;
const FIBER_SLOTS: usize = 4;
const C1_COLUMNS: usize = 49;
const C2_COLUMNS: usize = 2;
const C1_LEAF_BYTES: usize = FIBER_SLOTS * C1_COLUMNS * 4;
const C2_LEAF_BYTES: usize = C2_COLUMNS * FIBER_SLOTS * 16;
const C1_TAG: u8 = 0x40;
const C2_TAG: u8 = 0xc0;

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

    fn qm31(&mut self) -> SecureField {
        SecureField::from_m31(self.m31(), self.m31(), self.m31(), self.m31())
    }
}

fn fixture() -> (Vec<Vec<M31>>, Vec<Vec<SecureField>>) {
    let mut rng = Rng(0x4349_5243_4c45_4332);
    let c1 = (0..C1_COLUMNS)
        .map(|column| {
            (0..TRACE_LEN)
                .map(|row| {
                    rng.m31() + M31::from_u32_unchecked((column * 65_537 + row * 257 + 1) as u32)
                })
                .collect()
        })
        .collect();
    let c2 = (0..C2_COLUMNS)
        .map(|helper| {
            (0..TRACE_LEN)
                .map(|row| {
                    let mut coordinates = rng.qm31().to_m31_array();
                    coordinates[0] += M31::from_u32_unchecked((helper * 4099 + row + 1) as u32);
                    SecureField::from_m31_array(coordinates)
                })
                .collect()
        })
        .collect();
    (c1, c2)
}

fn encode_m31(message: &[M31]) -> Vec<M31> {
    assert_eq!(message.len(), TRACE_LEN);
    let domain = CanonicCoset::new(12).circle_domain();
    let values = CpuCirclePoly::new(message.to_vec()).evaluate(domain).values;
    assert_eq!(values.len(), CODEWORD_LEN);
    values
}

fn encode_qm31_coordinatewise(message: &[SecureField]) -> Vec<SecureField> {
    let encoded = std::array::from_fn::<_, 4, _>(|coordinate| {
        let base = message
            .iter()
            .map(|value| value.to_m31_array()[coordinate])
            .collect::<Vec<_>>();
        encode_m31(&base)
    });
    (0..CODEWORD_LEN)
        .map(|index| {
            SecureField::from_m31(
                encoded[0][index],
                encoded[1][index],
                encoded[2][index],
                encoded[3][index],
            )
        })
        .collect()
}

fn c1_leaves(codewords: &[Vec<M31>]) -> Vec<Vec<u8>> {
    (0..FIBER_COUNT)
        .map(|fiber| {
            let mut leaf = Vec::with_capacity(C1_LEAF_BYTES);
            for slot in 0..FIBER_SLOTS {
                for codeword in codewords {
                    leaf.extend_from_slice(&codeword[4 * fiber + slot].0.to_le_bytes());
                }
            }
            assert_eq!(leaf.len(), C1_LEAF_BYTES);
            leaf
        })
        .collect()
}

fn put_qm31(bytes: &mut Vec<u8>, value: SecureField) {
    for coordinate in value.to_m31_array() {
        bytes.extend_from_slice(&coordinate.0.to_le_bytes());
    }
}

fn c2_leaves(codewords: &[Vec<SecureField>]) -> Vec<Vec<u8>> {
    (0..FIBER_COUNT)
        .map(|fiber| {
            let mut leaf = Vec::with_capacity(C2_LEAF_BYTES);
            for codeword in codewords {
                for slot in 0..FIBER_SLOTS {
                    put_qm31(&mut leaf, codeword[4 * fiber + slot]);
                }
            }
            assert_eq!(leaf.len(), C2_LEAF_BYTES);
            leaf
        })
        .collect()
}

fn sha256(input: &[u8]) -> [u8; 32] {
    const INITIAL: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];
    const K: [u32; 64] = [
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ];

    let mut padded = input.to_vec();
    let bit_len = (padded.len() as u64) * 8;
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    let mut state = INITIAL;
    for chunk in padded.chunks_exact(64) {
        let mut words = [0u32; 64];
        for (index, word) in words[..16].iter_mut().enumerate() {
            *word = u32::from_be_bytes(chunk[4 * index..4 * index + 4].try_into().unwrap());
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let sum1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ (!e & g);
            let temporary1 = h
                .wrapping_add(sum1)
                .wrapping_add(choose)
                .wrapping_add(K[index])
                .wrapping_add(words[index]);
            let sum0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temporary2 = sum0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temporary1);
            d = c;
            c = b;
            b = a;
            a = temporary1.wrapping_add(temporary2);
        }
        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }

    let mut digest = [0u8; 32];
    for (index, word) in state.into_iter().enumerate() {
        digest[4 * index..4 * index + 4].copy_from_slice(&word.to_be_bytes());
    }
    digest
}

fn digest_c1_codewords(codewords: &[Vec<M31>]) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(C1_COLUMNS * CODEWORD_LEN * 4);
    for codeword in codewords {
        for value in codeword {
            bytes.extend_from_slice(&value.0.to_le_bytes());
        }
    }
    sha256(&bytes)
}

fn digest_c2_codewords(codewords: &[Vec<SecureField>]) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(C2_COLUMNS * CODEWORD_LEN * 16);
    for codeword in codewords {
        for &value in codeword {
            put_qm31(&mut bytes, value);
        }
    }
    sha256(&bytes)
}

fn digest_leaves(leaves: &[Vec<u8>]) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(leaves.iter().map(Vec::len).sum());
    for leaf in leaves {
        bytes.extend_from_slice(leaf);
    }
    sha256(&bytes)
}

fn radix4_root(tag: u8, leaves: &[Vec<u8>]) -> [u8; 32] {
    let mut level = leaves
        .iter()
        .map(|leaf| {
            let mut input = Vec::with_capacity(2 + leaf.len());
            input.extend_from_slice(&[0x10, tag]);
            input.extend_from_slice(leaf);
            sha256(&input)
        })
        .collect::<Vec<_>>();
    while level.len() > 1 {
        assert_eq!(level.len() % 4, 0);
        level = level
            .chunks_exact(4)
            .map(|children| {
                let mut input = Vec::with_capacity(129);
                input.push(0x12);
                for child in children {
                    input.extend_from_slice(child);
                }
                sha256(&input)
            })
            .collect();
    }
    level[0]
}

fn hex(bytes: [u8; 32]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(64);
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    output
}

fn main() {
    // Self-check the dependency-free SHA-256 before using it as an anchor.
    assert_eq!(
        hex(sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );

    let (c1_messages, c2_messages) = fixture();
    let c1_codewords = c1_messages
        .iter()
        .map(|message| encode_m31(message))
        .collect::<Vec<_>>();
    let c2_codewords = c2_messages
        .iter()
        .map(|message| encode_qm31_coordinatewise(message))
        .collect::<Vec<_>>();
    let c1_leaves = c1_leaves(&c1_codewords);
    let c2_leaves = c2_leaves(&c2_codewords);

    let values = [
        digest_c1_codewords(&c1_codewords),
        digest_c2_codewords(&c2_codewords),
        digest_leaves(&c1_leaves),
        digest_leaves(&c2_leaves),
        radix4_root(C1_TAG, &c1_leaves),
        radix4_root(C2_TAG, &c2_leaves),
    ];
    let mut anchor = b"aspis:official-stwo-circle-candidate-digests:v1".to_vec();
    for value in values {
        anchor.extend_from_slice(&value);
    }
    let fixture_digest = sha256(&anchor);

    println!("{{");
    println!("  \"c1_codewords_sha256\": \"{}\",", hex(values[0]));
    println!("  \"c2_codewords_sha256\": \"{}\",", hex(values[1]));
    println!("  \"c1_leaves_sha256\": \"{}\",", hex(values[2]));
    println!("  \"c2_leaves_sha256\": \"{}\",", hex(values[3]));
    println!("  \"c1_root\": \"{}\",", hex(values[4]));
    println!("  \"c2_root\": \"{}\",", hex(values[5]));
    println!("  \"fixture_sha256\": \"{}\"", hex(fixture_digest));
    println!("}}");
}
