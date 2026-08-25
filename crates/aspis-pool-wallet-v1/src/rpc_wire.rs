//! Dependency-free strict decoders for Solana RPC binary strings.
//!
//! JSON-encoded Solana messages carry public keys, blockhashes, signatures and
//! compiled-instruction data in base58. Transaction return data may be tagged
//! base58 or base64; raw account data is base64. These routines reject
//! non-alphabet bytes, overflow, non-canonical base58 zero prefixes, misplaced
//! padding and nonzero base64 pad bits while bounding allocation before
//! decoding untrusted RPC input.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RpcBinaryDecodeErrorV1 {
    LengthOverflow,
    EncodedLengthExceeded,
    DecodedLengthExceeded,
    WrongDecodedLength,
    InvalidBase58Character,
    NonCanonicalBase58,
    InvalidBase64Length,
    InvalidBase64Character,
    InvalidBase64Padding,
    NonCanonicalBase64PadBits,
}

fn base58_value(byte: u8) -> Option<u8> {
    match byte {
        b'1'..=b'9' => Some(byte - b'1'),
        b'A'..=b'H' => Some(byte - b'A' + 9),
        b'J'..=b'N' => Some(byte - b'J' + 17),
        b'P'..=b'Z' => Some(byte - b'P' + 22),
        b'a'..=b'k' => Some(byte - b'a' + 33),
        b'm'..=b'z' => Some(byte - b'm' + 44),
        _ => None,
    }
}

/// Decode one canonical Bitcoin/Solana base58 string with an exact output
/// allocation ceiling. Empty input canonically represents an empty byte slice.
pub fn decode_base58_bounded_v1(
    input: &str,
    max_decoded_bytes: usize,
) -> Result<Vec<u8>, RpcBinaryDecodeErrorV1> {
    let max_encoded_bytes = max_decoded_bytes
        .checked_mul(138)
        .and_then(|length| length.checked_div(100))
        .and_then(|length| length.checked_add(2))
        .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
    if input.len() > max_encoded_bytes {
        return Err(RpcBinaryDecodeErrorV1::EncodedLengthExceeded);
    }

    let encoded = input.as_bytes();
    let leading_zeroes = encoded.iter().take_while(|byte| **byte == b'1').count();
    if leading_zeroes > max_decoded_bytes {
        return Err(RpcBinaryDecodeErrorV1::DecodedLengthExceeded);
    }

    // Significant bytes are accumulated little-endian. Leading base58 zeroes
    // are skipped and restored exactly once below, which makes redundant `1`
    // prefixes impossible to accept.
    let mut significant = Vec::<u8>::new();
    for byte in &encoded[leading_zeroes..] {
        let value =
            u32::from(base58_value(*byte).ok_or(RpcBinaryDecodeErrorV1::InvalidBase58Character)?);
        let mut carry = value;
        for digit in &mut significant {
            let expanded = u32::from(*digit)
                .checked_mul(58)
                .and_then(|product| product.checked_add(carry))
                .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
            *digit = expanded as u8;
            carry = expanded >> 8;
        }
        while carry != 0 {
            let decoded_length = leading_zeroes
                .checked_add(significant.len())
                .and_then(|length| length.checked_add(1))
                .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
            if decoded_length > max_decoded_bytes {
                return Err(RpcBinaryDecodeErrorV1::DecodedLengthExceeded);
            }
            significant.push(carry as u8);
            carry >>= 8;
        }
    }

    // The significant positional representation must not itself start with a
    // zero byte. That would admit an alternate spelling of the same bytes.
    if significant.last().copied() == Some(0) {
        return Err(RpcBinaryDecodeErrorV1::NonCanonicalBase58);
    }
    let decoded_length = leading_zeroes
        .checked_add(significant.len())
        .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
    if decoded_length > max_decoded_bytes {
        return Err(RpcBinaryDecodeErrorV1::DecodedLengthExceeded);
    }
    let mut output = Vec::with_capacity(decoded_length);
    output.resize(leading_zeroes, 0);
    output.extend(significant.iter().rev());
    Ok(output)
}

/// Decode a canonical base58 value whose decoded width is fixed by the Solana
/// wire type, such as a 32-byte address/hash or 64-byte signature.
pub fn decode_base58_fixed_v1<const N: usize>(
    input: &str,
) -> Result<[u8; N], RpcBinaryDecodeErrorV1> {
    let decoded = decode_base58_bounded_v1(input, N)?;
    decoded
        .try_into()
        .map_err(|_| RpcBinaryDecodeErrorV1::WrongDecodedLength)
}

fn base64_value(byte: u8) -> Option<u8> {
    match byte {
        b'A'..=b'Z' => Some(byte - b'A'),
        b'a'..=b'z' => Some(byte - b'a' + 26),
        b'0'..=b'9' => Some(byte - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

/// Decode strict RFC 4648 standard base64 as emitted by Solana RPC. Padding
/// is required whenever the final quantum is partial.
pub fn decode_base64_standard_bounded_v1(
    input: &str,
    max_decoded_bytes: usize,
) -> Result<Vec<u8>, RpcBinaryDecodeErrorV1> {
    if !input.len().is_multiple_of(4) {
        return Err(RpcBinaryDecodeErrorV1::InvalidBase64Length);
    }
    let max_encoded_bytes = max_decoded_bytes
        .checked_add(2)
        .and_then(|length| length.checked_div(3))
        .and_then(|length| length.checked_mul(4))
        .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
    if input.len() > max_encoded_bytes {
        return Err(RpcBinaryDecodeErrorV1::EncodedLengthExceeded);
    }

    let encoded = input.as_bytes();
    let mut output = Vec::with_capacity(core::cmp::min(max_decoded_bytes, input.len() / 4 * 3));
    for (chunk_index, chunk) in encoded.chunks_exact(4).enumerate() {
        let is_last = chunk_index + 1 == encoded.len() / 4;
        let a = base64_value(chunk[0]).ok_or(RpcBinaryDecodeErrorV1::InvalidBase64Character)?;
        let b = base64_value(chunk[1]).ok_or(RpcBinaryDecodeErrorV1::InvalidBase64Character)?;

        let padding = match (chunk[2], chunk[3]) {
            (b'=', b'=') => 2,
            (_, b'=') => 1,
            (b'=', _) => return Err(RpcBinaryDecodeErrorV1::InvalidBase64Padding),
            _ => 0,
        };
        if padding != 0 && !is_last {
            return Err(RpcBinaryDecodeErrorV1::InvalidBase64Padding);
        }
        let c = if padding == 2 {
            0
        } else {
            base64_value(chunk[2]).ok_or(RpcBinaryDecodeErrorV1::InvalidBase64Character)?
        };
        let d = if padding == 0 {
            base64_value(chunk[3]).ok_or(RpcBinaryDecodeErrorV1::InvalidBase64Character)?
        } else {
            0
        };
        if padding == 2 && b & 0x0f != 0 {
            return Err(RpcBinaryDecodeErrorV1::NonCanonicalBase64PadBits);
        }
        if padding == 1 && c & 0x03 != 0 {
            return Err(RpcBinaryDecodeErrorV1::NonCanonicalBase64PadBits);
        }

        let produced = 3usize
            .checked_sub(padding)
            .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
        let new_length = output
            .len()
            .checked_add(produced)
            .ok_or(RpcBinaryDecodeErrorV1::LengthOverflow)?;
        if new_length > max_decoded_bytes {
            return Err(RpcBinaryDecodeErrorV1::DecodedLengthExceeded);
        }
        output.push((a << 2) | (b >> 4));
        if padding < 2 {
            output.push((b << 4) | (c >> 2));
        }
        if padding == 0 {
            output.push((c << 6) | d);
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base58_decodes_fixed_solana_widths_and_rejects_alternate_or_invalid_spelling() {
        assert_eq!(
            decode_base58_fixed_v1::<32>("11111111111111111111111111111111"),
            Ok([0u8; 32])
        );
        assert_eq!(decode_base58_bounded_v1("2", 1), Ok(vec![1]));
        assert_eq!(decode_base58_bounded_v1("z", 1), Ok(vec![57]));
        assert_eq!(decode_base58_bounded_v1("21", 1), Ok(vec![58]));
        assert_eq!(
            decode_base58_fixed_v1::<32>("1111111111111111111111111111111"),
            Err(RpcBinaryDecodeErrorV1::WrongDecodedLength)
        );
        assert_eq!(
            decode_base58_bounded_v1("0", 1),
            Err(RpcBinaryDecodeErrorV1::InvalidBase58Character)
        );
        assert_eq!(
            decode_base58_bounded_v1("O0Il", 8),
            Err(RpcBinaryDecodeErrorV1::InvalidBase58Character)
        );
        assert_eq!(
            decode_base58_bounded_v1("111", 2),
            Err(RpcBinaryDecodeErrorV1::DecodedLengthExceeded)
        );
    }

    #[test]
    fn base64_matches_rfc4648_and_rejects_padding_aliases_whitespace_and_overflow() {
        assert_eq!(decode_base64_standard_bounded_v1("", 0), Ok(vec![]));
        assert_eq!(
            decode_base64_standard_bounded_v1("Zg==", 1),
            Ok(b"f".to_vec())
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Zm8=", 2),
            Ok(b"fo".to_vec())
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Zm9v", 3),
            Ok(b"foo".to_vec())
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Zh==", 1),
            Err(RpcBinaryDecodeErrorV1::NonCanonicalBase64PadBits)
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Zm9=", 2),
            Err(RpcBinaryDecodeErrorV1::NonCanonicalBase64PadBits)
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Zg=", 1),
            Err(RpcBinaryDecodeErrorV1::InvalidBase64Length)
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Z g=", 4),
            Err(RpcBinaryDecodeErrorV1::InvalidBase64Character)
        );
        assert_eq!(
            decode_base64_standard_bounded_v1("Zg==", 0),
            Err(RpcBinaryDecodeErrorV1::EncodedLengthExceeded)
        );
    }
}
