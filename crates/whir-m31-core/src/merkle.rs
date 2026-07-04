use solana_program::hash::hashv;

pub type MerkleHash = [u8; 32];

const LEAF_PREFIX: &[u8] = b"whir-m31/leaf/v0";
const NODE_PREFIX: &[u8] = b"whir-m31/node/v0";

pub fn hash_leaf(bytes: &[u8]) -> MerkleHash {
    hashv(&[LEAF_PREFIX, bytes]).to_bytes()
}

pub fn hash_node(left: &MerkleHash, right: &MerkleHash) -> MerkleHash {
    hashv(&[NODE_PREFIX, left, right]).to_bytes()
}

pub fn verify_path_bytes(
    leaf_hash: MerkleHash,
    mut index: usize,
    siblings_bytes: &[u8],
    expected_root: &MerkleHash,
) -> bool {
    if siblings_bytes.len() % 32 != 0 {
        return false;
    }
    let mut current = leaf_hash;
    for chunk in siblings_bytes.chunks_exact(32) {
        let mut sibling = [0_u8; 32];
        sibling.copy_from_slice(chunk);
        current = if index & 1 == 0 {
            hash_node(&current, &sibling)
        } else {
            hash_node(&sibling, &current)
        };
        index >>= 1;
    }
    &current == expected_root
}
