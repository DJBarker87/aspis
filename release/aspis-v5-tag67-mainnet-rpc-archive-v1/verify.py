#!/usr/bin/env python3
"""Offline integrity and completeness checks for the V5 mainnet RPC archive."""

from __future__ import annotations

import base64
import hashlib
import json
import struct
import tarfile
from pathlib import Path, PurePosixPath
from typing import Any


ROOT = Path(__file__).resolve().parent
INDEX_PATH = ROOT / "rpc-cache/index.json"
ARCHIVE_PATH = ROOT / "rpc-cache/payer-full-rpc-responses.tar.gz"
SUMMARY_PATH = ROOT / "rpc-cache/archive-summary.json"
BINDING_PATH = ROOT / "release-binding.json"
MANIFEST_PATH = ROOT / "manifest.json"
CHECKSUM_PATH = ROOT / "SHA256SUMS"
EXPECTED_GENESIS = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d"
BASE58 = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
BASE58_INDEX = {character: index for index, character in enumerate(BASE58)}
LOADER_ID = "BPFLoaderUpgradeab1e11111111111111111111111"
SYSTEM_ID = "11111111111111111111111111111111"
COMPUTE_BUDGET_ID = "ComputeBudget111111111111111111111111111111"
RENT_SYSVAR_ID = "SysvarRent111111111111111111111111111111111"
CLOCK_SYSVAR_ID = "SysvarC1ock11111111111111111111111111111111"
PROOF_ACCOUNT_HEADER_BYTES = 40
BUFFER_ACCOUNT_HEADER_BYTES = 37
UPLOAD_CHUNK_BYTES = 960


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_bytes())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"could not read {path.relative_to(ROOT)}: {error}")


def base58_encode(raw: bytes) -> str:
    zeroes = len(raw) - len(raw.lstrip(b"\0"))
    number = int.from_bytes(raw, "big")
    encoded = bytearray()
    while number:
        number, remainder = divmod(number, 58)
        encoded.append(BASE58[remainder])
    encoded.reverse()
    return (BASE58[:1] * zeroes + encoded).decode("ascii")


def base58_decode(encoded: str) -> bytes:
    number = 0
    try:
        for character in encoded.encode("ascii"):
            number = number * 58 + BASE58_INDEX[character]
    except (KeyError, UnicodeEncodeError) as error:
        fail(f"invalid base58 value: {error}")
    raw = number.to_bytes((number.bit_length() + 7) // 8, "big") if number else b""
    zeroes = len(encoded) - len(encoded.lstrip("1"))
    return b"\0" * zeroes + raw


def read_shortvec(raw: bytes, offset: int = 0) -> tuple[int, int]:
    value = 0
    shift = 0
    while True:
        if offset >= len(raw) or shift > 21:
            fail("invalid short-vector length in transaction wire")
        byte = raw[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if byte & 0x80 == 0:
            return value, offset
        shift += 7


def parse_legacy_transaction(wire: bytes) -> dict[str, Any]:
    signature_count, offset = read_shortvec(wire)
    signature_end = offset + 64 * signature_count
    if signature_count < 1 or signature_end > len(wire):
        fail("invalid signed transaction wire")
    signatures = [
        base58_encode(wire[offset + 64 * index : offset + 64 * (index + 1)])
        for index in range(signature_count)
    ]
    offset = signature_end
    message_start = offset
    if offset >= len(wire):
        fail("signed transaction has no message")
    if wire[offset] & 0x80:
        fail("archive unexpectedly contains a versioned transaction")
    if offset + 3 > len(wire):
        fail("truncated legacy message header")
    header = tuple(wire[offset : offset + 3])
    offset += 3
    if header[0] != signature_count:
        fail("message required-signature count differs from signed wire")

    key_count, offset = read_shortvec(wire, offset)
    key_end = offset + 32 * key_count
    if key_end + 32 > len(wire):
        fail("truncated legacy account-key or blockhash section")
    keys = [
        base58_encode(wire[offset + 32 * index : offset + 32 * (index + 1)])
        for index in range(key_count)
    ]
    if header[1] > header[0] or header[2] > key_count - header[0]:
        fail("legacy message has impossible readonly-account counts")
    offset = key_end + 32  # recent blockhash
    instruction_count, offset = read_shortvec(wire, offset)
    instructions: list[dict[str, Any]] = []
    for _ in range(instruction_count):
        if offset >= len(wire):
            fail("truncated compiled instruction")
        program_index = wire[offset]
        offset += 1
        account_count, offset = read_shortvec(wire, offset)
        account_end = offset + account_count
        if account_end > len(wire):
            fail("truncated compiled-instruction account list")
        account_indices = list(wire[offset:account_end])
        offset = account_end
        data_length, offset = read_shortvec(wire, offset)
        data_end = offset + data_length
        if data_end > len(wire):
            fail("truncated compiled-instruction data")
        if program_index >= key_count or any(index >= key_count for index in account_indices):
            fail("compiled instruction contains an out-of-range account index")
        instructions.append(
            {
                "program": keys[program_index],
                "program_index": program_index,
                "accounts": [keys[index] for index in account_indices],
                "account_indices": account_indices,
                "data": wire[offset:data_end],
            }
        )
        offset = data_end
    if offset != len(wire):
        fail("legacy transaction contains trailing bytes")
    return {
        "signatures": signatures,
        "header": header,
        "keys": keys,
        "instructions": instructions,
        "message": wire[message_start:],
    }


def key_is_signer(message: dict[str, Any], key: str) -> bool:
    try:
        index = message["keys"].index(key)
    except ValueError:
        return False
    return index < message["header"][0]


def key_is_writable(message: dict[str, Any], key: str) -> bool:
    try:
        index = message["keys"].index(key)
    except ValueError:
        return False
    required, readonly_signed, readonly_unsigned = message["header"]
    if index < required:
        return index < required - readonly_signed
    return index < len(message["keys"]) - readonly_unsigned


def successful_instruction_events(
    decoded_transactions: list[dict[str, Any]], program: str
) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    return [
        (transaction, instruction)
        for transaction in decoded_transactions
        if transaction["result"]["meta"]["err"] is None
        for instruction in transaction["message"]["instructions"]
        if instruction["program"] == program
    ]


def decode_system_create(data: bytes) -> tuple[int, int, bytes]:
    if len(data) != 52 or struct.unpack_from("<I", data)[0] != 0:
        fail("expected an exact System CreateAccount instruction")
    _, lamports, space = struct.unpack_from("<IQQ", data)
    return lamports, space, data[20:52]


def reconstruct_uploaded_proof(
    decoded_transactions: list[dict[str, Any]],
    binding: dict[str, Any],
    lifecycle: dict[str, Any],
    proof_path: Path,
    statement_path: Path,
) -> dict[str, Any]:
    identities = lifecycle["identities"]
    program = identities["program"]
    proof_account = identities["proof_account"]
    payer = identities["payer"]
    pool = identities["pool"]
    nullifier = identities["nullifier"]
    proof = proof_path.read_bytes()
    statement = load_json(statement_path)

    all_program_events = successful_instruction_events(decoded_transactions, program)
    proof_events = [
        event for event in all_program_events if proof_account in event[1]["accounts"]
    ]
    by_tag: dict[int, list[tuple[dict[str, Any], dict[str, Any]]]] = {}
    for event in proof_events:
        data = event[1]["data"]
        if not data:
            fail("empty program instruction involving the proof account")
        by_tag.setdefault(data[0], []).append(event)
    expected_counts = {0: 1, 1: 79, 62: 1, 64: 1, 67: 1}
    if {tag: len(events) for tag, events in by_tag.items()} != expected_counts:
        fail("proof-account lifecycle instruction counts differ from 1+79+1+1+1")

    init_transaction, init_instruction = by_tag[0][0]
    if (
        init_instruction["accounts"] != [proof_account, payer]
        or len(init_instruction["data"]) != 5
        or struct.unpack_from("<I", init_instruction["data"], 1)[0] != len(proof)
        or not key_is_signer(init_transaction["message"], proof_account)
        or not key_is_signer(init_transaction["message"], payer)
        or not key_is_writable(init_transaction["message"], proof_account)
    ):
        fail("proof tag-0 initialization shape differs from the released proof")
    proof_creates = [
        instruction
        for instruction in init_transaction["message"]["instructions"]
        if instruction["program"] == SYSTEM_ID
        and instruction["accounts"] == [payer, proof_account]
    ]
    if len(proof_creates) != 1:
        fail("proof initialization transaction has no unique System CreateAccount")
    _, proof_space, proof_owner = decode_system_create(proof_creates[0]["data"])
    if proof_space != len(proof) + PROOF_ACCOUNT_HEADER_BYTES:
        fail("proof-account allocation length differs from header plus released proof")
    if base58_encode(proof_owner) != program:
        fail("proof-account System CreateAccount owner differs from deployed program")

    chunks: list[tuple[int, bytes, dict[str, Any]]] = []
    for transaction, instruction in by_tag[1]:
        data = instruction["data"]
        if len(data) < 9 or instruction["accounts"] != [proof_account, payer]:
            fail("malformed proof upload instruction")
        offset, chunk_length = struct.unpack_from("<II", data, 1)
        chunk = data[9:]
        if len(chunk) != chunk_length or not key_is_signer(transaction["message"], payer):
            fail("proof upload length or authority signer differs")
        if not key_is_writable(transaction["message"], proof_account):
            fail("proof upload did not mark the proof account writable")
        chunks.append((offset, chunk, transaction))
    chunks.sort(key=lambda item: item[0])
    cursor = 0
    reconstructed = bytearray()
    for index, (offset, chunk, _) in enumerate(chunks):
        expected_length = min(UPLOAD_CHUNK_BYTES, len(proof) - cursor)
        if offset != cursor or len(chunk) != expected_length:
            fail(f"proof upload chunk {index} is non-contiguous or has the wrong length")
        reconstructed.extend(chunk)
        cursor += len(chunk)
    if bytes(reconstructed) != proof:
        fail("proof reconstructed from finalized uploads differs from released proof")

    finalize_transaction, finalize_instruction = by_tag[62][0]
    if (
        finalize_instruction["data"] != b">"
        or finalize_instruction["accounts"] != [proof_account, payer]
        or not key_is_signer(finalize_transaction["message"], payer)
        or not key_is_writable(finalize_transaction["message"], proof_account)
    ):
        fail("proof tag-62 finalization shape differs")
    tag67_transaction, tag67_instruction = by_tag[67][0]
    tag67_named = binding["named_transactions"]["tag67"]
    if (
        tag67_transaction["row"]["signature"] != tag67_named["signature"]
        or tag67_instruction["accounts"]
        != [proof_account, pool, nullifier, payer, SYSTEM_ID]
        or len(tag67_instruction["data"]) != 169
        or not key_is_signer(tag67_transaction["message"], payer)
        or key_is_writable(tag67_transaction["message"], proof_account)
        or not key_is_writable(tag67_transaction["message"], pool)
        or not key_is_writable(tag67_transaction["message"], nullifier)
    ):
        fail("named tag-67 transaction does not consume the reconstructed proof as recorded")
    tag67_record = lifecycle["transactions"]["tag67"]
    if (
        digest(tag67_transaction["wire"]) != tag67_record["wire_sha256"]
        or digest(tag67_transaction["message"]["message"])
        != tag67_record["message_sha256"]
        or digest(tag67_instruction["data"]) != tag67_record["instruction_sha256"]
        or tag67_transaction["result"]["meta"].get("computeUnitsConsumed")
        != tag67_record["landed_compute_units"]
    ):
        fail("archived tag-67 wire, instruction, or compute evidence differs from release")
    close_transaction, close_instruction = by_tag[64][0]
    close_named = binding["named_transactions"]["proof_close_tag64"]
    if (
        close_transaction["row"]["signature"] != close_named["signature"]
        or close_instruction["data"] != b"@"
        or close_instruction["accounts"] != [proof_account, payer]
        or not key_is_signer(close_transaction["message"], proof_account)
        or not key_is_signer(close_transaction["message"], payer)
        or not key_is_writable(close_transaction["message"], proof_account)
        or not key_is_writable(close_transaction["message"], payer)
    ):
        fail("named tag-64 proof close differs from the recorded lifecycle")

    upload_slots = [transaction["result"]["slot"] for _, _, transaction in chunks]
    ordered_slots = (
        init_transaction["result"]["slot"],
        min(upload_slots),
        max(upload_slots),
        finalize_transaction["result"]["slot"],
        tag67_transaction["result"]["slot"],
        close_transaction["result"]["slot"],
    )
    if not (
        ordered_slots[0] < ordered_slots[1]
        and ordered_slots[2] < ordered_slots[3] < ordered_slots[4] < ordered_slots[5]
    ):
        fail("proof lifecycle slots are not initialize, uploads, seal, spend, close")

    tag67_data = tag67_instruction["data"]
    public_fields = {
        "current_anchor_hex": tag67_data[1:33].hex(),
        "nullifier_hex": tag67_data[33:65].hex(),
        "output_commitment_hex": tag67_data[65:97].hex(),
        "output_anchor_hex": tag67_data[97:129].hex(),
        "asset_id": struct.unpack_from("<I", tag67_data, 129)[0],
        "fee": struct.unpack_from("<I", tag67_data, 133)[0],
        "deployment_domain_hex": tag67_data[137:169].hex(),
    }
    for field, expected in public_fields.items():
        if statement.get(field) != expected:
            fail(f"released statement field differs from tag-67 wire: {field}")
    if statement.get("pool_hex") != base58_decode(pool).hex():
        fail("released statement pool differs from tag-67 pool account")

    pool_init_events = [
        event
        for event in all_program_events
        if event[1]["data"][:1] == bytes([63]) and event[1]["accounts"] == [pool]
    ]
    if len(pool_init_events) != 1:
        fail("pool has no unique successful tag-63 initialization in the archive")
    pool_init_data = pool_init_events[0][1]["data"]
    if len(pool_init_data) < 45:
        fail("pool tag-63 initialization is truncated")
    sequence = struct.unpack_from("<Q", pool_init_data, 1)[0]
    domain_tag_length = struct.unpack_from("<I", pool_init_data, 41)[0]
    domain_tag = pool_init_data[45:]
    if len(domain_tag) != domain_tag_length:
        fail("pool tag-63 deployment-domain tag length differs")
    expected_domain = hashlib.sha256(
        b"aspis-spend-deployment-domain-v1" + base58_decode(program) + domain_tag
    ).hexdigest()
    if (
        statement.get("sequence") != sequence
        or statement.get("current_anchor_hex") != pool_init_data[9:41].hex()
        or statement.get("deployment_domain_hex") != expected_domain
        or domain_tag != b"mainnet-beta"
    ):
        fail("released statement differs from the archived pool initialization")

    sealed_image = b"ASPU" + struct.pack("<I", len(proof)) + b"\0" * 32 + proof
    return {
        "proof_bytes": len(proof),
        "proof_sha256": digest(proof),
        "upload_transactions": len(chunks),
        "sealed_account_bytes": len(sealed_image),
        "sealed_account_sha256": digest(sealed_image),
        "statement_sha256": digest(statement_path.read_bytes()),
    }


def reconstruct_deployed_program(
    decoded_transactions: list[dict[str, Any]],
    binding: dict[str, Any],
    lifecycle: dict[str, Any],
    release_manifest: dict[str, Any],
    release_root: Path,
) -> dict[str, Any]:
    identities = lifecycle["identities"]
    program = identities["program"]
    programdata = identities["programdata"]
    payer = identities["payer"]
    deployment_named = binding["named_transactions"]["deployment"]
    deployment_matches = [
        transaction
        for transaction in decoded_transactions
        if transaction["row"]["signature"] == deployment_named["signature"]
    ]
    if len(deployment_matches) != 1:
        fail("named deployment transaction is not unique")
    deployment = deployment_matches[0]
    loader_deploys = [
        instruction
        for instruction in deployment["message"]["instructions"]
        if instruction["program"] == LOADER_ID
        and len(instruction["data"]) == 12
        and struct.unpack_from("<I", instruction["data"])[0] == 2
    ]
    if len(loader_deploys) != 1 or deployment["result"]["meta"]["err"] is not None:
        fail("named deployment has no unique successful deployWithMaxDataLen")
    deploy_instruction = loader_deploys[0]
    max_data_len = struct.unpack_from("<Q", deploy_instruction["data"], 4)[0]
    if len(deploy_instruction["accounts"]) != 8:
        fail("deployWithMaxDataLen account list differs")
    (
        deploy_payer,
        deploy_programdata,
        deploy_program,
        buffer,
        rent_sysvar,
        clock_sysvar,
        system_program,
        authority,
    ) = deploy_instruction["accounts"]
    if (
        deploy_payer != payer
        or deploy_programdata != programdata
        or deploy_program != program
        or rent_sysvar != RENT_SYSVAR_ID
        or clock_sysvar != CLOCK_SYSVAR_ID
        or system_program != SYSTEM_ID
        or not key_is_signer(deployment["message"], payer)
        or not key_is_signer(deployment["message"], program)
        or not key_is_signer(deployment["message"], authority)
        or not key_is_writable(deployment["message"], programdata)
        or not key_is_writable(deployment["message"], program)
        or not key_is_writable(deployment["message"], buffer)
    ):
        fail("deployWithMaxDataLen identities, sysvars, or signers differ")

    candidate = release_manifest["frozen_candidate"]
    sbf_path = (release_root / candidate["sbf_path"]).resolve()
    if (
        not sbf_path.is_file()
        or sbf_path.stat().st_size != candidate["sbf_bytes"]
        or digest(sbf_path.read_bytes()) != candidate["sbf_sha256"]
    ):
        fail("frozen-candidate SBF differs from the mainnet release manifest")
    sbf = sbf_path.read_bytes()
    if max_data_len < len(sbf):
        fail("deployWithMaxDataLen is shorter than the released SBF")

    loader_events = successful_instruction_events(decoded_transactions, LOADER_ID)
    buffer_events = [
        event for event in loader_events if buffer in event[1]["accounts"]
    ]
    initializations = [
        event
        for event in buffer_events
        if event[1]["data"] == b"\0\0\0\0"
        and event[1]["accounts"] == [buffer, authority]
    ]
    writes = [
        event
        for event in buffer_events
        if len(event[1]["data"]) >= 4
        and struct.unpack_from("<I", event[1]["data"])[0] == 1
    ]
    if (
        len(initializations) != 1
        or len(writes) != 1466
        or len(buffer_events) != 1468
        or len({event[0]["row"]["signature"] for event in writes}) != len(writes)
    ):
        fail("deployment buffer history differs from one initialize plus 1,466 writes")
    init_transaction, _ = initializations[0]
    if (
        not key_is_signer(init_transaction["message"], payer)
        or not key_is_signer(init_transaction["message"], buffer)
        or not key_is_writable(init_transaction["message"], buffer)
    ):
        fail("deployment buffer initialization signers or access differ")
    buffer_creates = [
        instruction
        for instruction in init_transaction["message"]["instructions"]
        if instruction["program"] == SYSTEM_ID
        and instruction["accounts"] == [payer, buffer]
    ]
    if len(buffer_creates) != 1:
        fail("buffer initialization transaction has no unique System CreateAccount")
    _, buffer_space, buffer_owner = decode_system_create(buffer_creates[0]["data"])
    if buffer_space != len(sbf) + BUFFER_ACCOUNT_HEADER_BYTES:
        fail("deployment buffer allocation differs from SBF plus loader header")
    if base58_encode(buffer_owner) != LOADER_ID:
        fail("deployment buffer owner is not the upgradeable loader")

    image = bytearray(len(sbf))
    covered = bytearray(len(sbf))
    chunks: list[tuple[int, int]] = []
    exact_duplicate_chunks = 0
    duplicate_bytes = 0
    for transaction, instruction in writes:
        data = instruction["data"]
        if instruction["accounts"] != [buffer, authority] or len(data) < 16:
            fail("loader Write accounts or payload are malformed")
        variant, offset, payload_length = struct.unpack_from("<IIQ", data)
        payload = data[16:]
        if variant != 1 or len(payload) != payload_length:
            fail("loader Write encoding differs from u32/u32/u64/payload")
        if not key_is_signer(transaction["message"], authority):
            fail("loader Write authority is not a required signer")
        if not key_is_writable(transaction["message"], buffer):
            fail("loader Write buffer is not writable")
        end = offset + payload_length
        if end > len(image):
            fail("loader Write exceeds released SBF length")
        already_covered = sum(covered[offset:end])
        if already_covered:
            if already_covered != payload_length or image[offset:end] != payload:
                fail("loader Write history contains a partial or conflicting overlap")
            exact_duplicate_chunks += 1
            duplicate_bytes += payload_length
        else:
            image[offset:end] = payload
            covered[offset:end] = b"\1" * payload_length
        chunks.append((offset, payload_length))
    if (
        covered.count(0) != 0
        or sum(length for _, length in chunks) - duplicate_bytes != len(sbf)
        or exact_duplicate_chunks != 9
    ):
        fail("loader Write history has gaps or an unexpected exact-duplicate count")
    if bytes(image) != sbf:
        fail("SBF reconstructed from finalized loader writes differs from frozen candidate")

    init_slot = init_transaction["result"]["slot"]
    write_slots = [transaction["result"]["slot"] for transaction, _ in writes]
    deploy_slot = deployment["result"]["slot"]
    if not (init_slot < min(write_slots) and max(write_slots) < deploy_slot):
        fail("deployment lifecycle slots are not initialize, writes, deploy")

    authority_bytes = base58_decode(authority)
    if len(authority_bytes) != 32:
        fail("deployment authority is not a 32-byte public key")
    programdata_header = struct.pack("<IQB", 3, deploy_slot, 1) + authority_bytes
    # Loader-v3 creates a zero-filled max-data account, writes its 45-byte
    # ProgramData state, and copies the shorter buffer body into its prefix.
    programdata_image = (
        programdata_header + sbf + b"\0" * (max_data_len - len(sbf))
    )
    return {
        "buffer": buffer,
        "upgrade_authority": authority,
        "write_transactions": len(writes),
        "exact_duplicate_writes": exact_duplicate_chunks,
        "unique_write_offsets": len(writes) - exact_duplicate_chunks,
        "sbf_bytes": len(sbf),
        "sbf_sha256": digest(sbf),
        "programdata_bytes": len(programdata_image),
        "programdata_sha256": digest(programdata_image),
        "programdata_header_hex": programdata_header.hex(),
        "max_data_len": max_data_len,
    }


def validate_rpc_response(
    raw: bytes,
    expected_id: str | int,
    *,
    require_result: bool = True,
) -> dict[str, Any]:
    try:
        response = json.loads(raw)
    except json.JSONDecodeError as error:
        fail(f"invalid JSON-RPC response for id {expected_id}: {error}")
    if not isinstance(response, dict) or response.get("jsonrpc") != "2.0":
        fail(f"invalid JSON-RPC envelope for id {expected_id}")
    if response.get("id") != expected_id:
        fail(f"JSON-RPC id mismatch for {expected_id}")
    if "error" in response or "result" not in response:
        fail(f"JSON-RPC error or missing result for id {expected_id}")
    if require_result and response["result"] is None:
        fail(f"null JSON-RPC result for id {expected_id}")
    return response


def main() -> int:
    index = load_json(INDEX_PATH)
    summary = load_json(SUMMARY_PATH)
    binding = load_json(BINDING_PATH)
    manifest = load_json(MANIFEST_PATH)

    for line in CHECKSUM_PATH.read_text(encoding="ascii").splitlines():
        expected, relative = line.split("  ", 1)
        path = ROOT / relative
        if not path.is_file() or digest(path.read_bytes()) != expected:
            fail(f"SHA256SUMS mismatch: {relative}")
    for relative, identity in manifest["objects"].items():
        path = ROOT / relative
        if (
            not path.is_file()
            or path.stat().st_size != identity["bytes"]
            or digest(path.read_bytes()) != identity["sha256"]
        ):
            fail(f"manifest object mismatch: {relative}")
    capture_tool = manifest["capture_tool"]
    capture_tool_path = (ROOT / capture_tool["path"]).resolve()
    if (
        not capture_tool_path.is_file()
        or capture_tool_path.stat().st_size != capture_tool["bytes"]
        or digest(capture_tool_path.read_bytes()) != capture_tool["sha256"]
    ):
        fail("capture tool differs from manifest identity")

    release = binding["mainnet_release"]
    release_root = (ROOT / release["path"]).resolve()
    release_manifest_path = release_root / "manifest.json"
    lifecycle_path = release_root / "evidence/mainnet-lifecycle.json"
    proof_path = (ROOT / release["proof"]["path"]).resolve()
    statement_path = (ROOT / release["statement"]["path"]).resolve()
    release_checks = [
        (
            release_manifest_path,
            None,
            release["manifest_sha256"],
            "mainnet release manifest",
        ),
        (
            lifecycle_path,
            None,
            release["lifecycle_sha256"],
            "mainnet lifecycle",
        ),
        (
            proof_path,
            release["proof"]["bytes"],
            release["proof"]["sha256"],
            "mainnet proof",
        ),
        (
            statement_path,
            release["statement"]["bytes"],
            release["statement"]["sha256"],
            "mainnet statement",
        ),
    ]
    for path, expected_bytes, expected_hash, label in release_checks:
        if (
            not path.is_file()
            or (expected_bytes is not None and path.stat().st_size != expected_bytes)
            or digest(path.read_bytes()) != expected_hash
        ):
            fail(f"{label} differs from release-binding.json")
    release_manifest = load_json(release_manifest_path)
    lifecycle = load_json(lifecycle_path)
    if (
        release_manifest.get("network") != "mainnet-beta"
        or lifecycle.get("network") != "mainnet-beta"
        or lifecycle.get("genesis_hash") != EXPECTED_GENESIS
    ):
        fail("bound release manifest or lifecycle is not mainnet-beta")
    release_mainnet = release_manifest["mainnet"]
    if (
        release_mainnet["program_id"] != lifecycle["identities"]["program"]
        or release_mainnet["proof_account"]
        != lifecycle["identities"]["proof_account"]
        or release_mainnet["deployment_signature"]
        != binding["named_transactions"]["deployment"]["signature"]
        or release_mainnet["tag67_signature"]
        != binding["named_transactions"]["tag67"]["signature"]
        or release_mainnet["tag67_finalized_slot"]
        != binding["named_transactions"]["tag67"]["slot"]
    ):
        fail("mainnet manifest, lifecycle, and archive binding identities differ")

    if digest(ARCHIVE_PATH.read_bytes()) != summary["sha256"]:
        fail("archive SHA-256 differs from archive-summary.json")
    if summary["sha256"] != binding["archive"]["sha256"]:
        fail("archive SHA-256 differs from release-binding.json")
    if ARCHIVE_PATH.stat().st_size != binding["archive"]["bytes"]:
        fail("archive byte length differs from release-binding.json")

    with tarfile.open(ARCHIVE_PATH, "r:gz") as archive:
        members = archive.getmembers()
        names = [member.name for member in members]
        if len(names) != len(set(names)):
            fail("archive contains duplicate member names")
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts or not member.isfile():
                fail(f"unsafe or non-file archive member: {member.name}")
        if len(members) != summary["members"]:
            fail("archive member count differs from archive-summary.json")
        raw_by_name = {
            member.name: archive.extractfile(member).read() for member in members
        }

    if raw_by_name.get("capture-index.json") != INDEX_PATH.read_bytes():
        fail("external index differs from archived capture-index.json")

    page_rows: list[dict[str, Any]] = []
    pages = index["pagination"]["pages"]
    if len(pages) != 2 or [page["result_count"] for page in pages] != [1000, 570]:
        fail("signature pagination is not the expected 1000 + 570")
    for page in pages:
        raw = raw_by_name.get(page["response_path"])
        if raw is None:
            fail(f"missing signature page {page['response_path']}")
        if len(raw) != page["response_bytes"] or digest(raw) != page["response_sha256"]:
            fail(f"signature-page identity mismatch: {page['response_path']}")
        response = validate_rpc_response(raw, page["request_id"])
        rows = response["result"]
        if len(rows) != page["result_count"]:
            fail(f"signature-page count mismatch: {page['response_path']}")
        page_rows.extend(rows)

    transactions = index["transactions"]
    if len(page_rows) != 1570 or len(transactions) != 1570:
        fail("archive does not contain exactly 1,570 indexed signatures")
    if [row["signature"] for row in page_rows] != [
        row["signature"] for row in transactions
    ]:
        fail("signature pages and transaction index are not in the same order")

    decoded_transactions: list[dict[str, Any]] = []
    for row in transactions:
        raw = raw_by_name.get(row["response_path"])
        if raw is None:
            fail(f"missing transaction response for {row['signature']}")
        if len(raw) != row["response_bytes"] or digest(raw) != row["response_sha256"]:
            fail(f"transaction response identity mismatch: {row['signature']}")
        response = validate_rpc_response(raw, row["index"])
        result = response["result"]
        if result.get("slot") != row["slot"] or result.get("blockTime") != row["block_time"]:
            fail(f"slot or block time mismatch: {row['signature']}")
        meta = result.get("meta")
        required_meta = {"err", "fee", "preBalances", "postBalances"}
        if not isinstance(meta, dict) or not required_meta.issubset(meta):
            fail(f"incomplete transaction metadata: {row['signature']}")
        encoded = result.get("transaction")
        if (
            not isinstance(encoded, list)
            or len(encoded) != 2
            or encoded[1] != "base64"
        ):
            fail(f"transaction is not full base64 wire data: {row['signature']}")
        try:
            wire = base64.b64decode(encoded[0], validate=True)
        except (ValueError, TypeError) as error:
            fail(f"invalid base64 transaction wire for {row['signature']}: {error}")
        message = parse_legacy_transaction(wire)
        if message["signatures"][0] != row["signature"]:
            fail(f"first wire signature mismatch: {row['signature']}")
        decoded_transactions.append(
            {"row": row, "result": result, "wire": wire, "message": message}
        )

    by_signature = {row["signature"]: row for row in transactions}
    for name, expected in binding["named_transactions"].items():
        row = by_signature.get(expected["signature"])
        if row is None or row["slot"] != expected["slot"]:
            fail(f"missing or mismatched named transaction: {name}")

    observations = {item["request_id"]: item for item in index["observations"]}
    genesis_item = observations.get("genesis-hash")
    if genesis_item is None:
        fail("genesis-hash observation is missing")
    genesis_raw = raw_by_name.get(genesis_item["response_path"])
    if genesis_raw is None:
        fail("genesis-hash response is missing")
    genesis = validate_rpc_response(genesis_raw, "genesis-hash")["result"]
    if genesis != EXPECTED_GENESIS or genesis != binding["genesis_hash"]:
        fail("genesis hash differs from mainnet-beta")

    for account in binding["closed_account_observations"]:
        request_id = f"account-{account}"
        item = observations.get(request_id)
        if item is None:
            fail(f"closed-account observation is missing: {account}")
        raw = raw_by_name.get(item["response_path"])
        if raw is None:
            fail(f"closed-account response is missing: {account}")
        result = validate_rpc_response(raw, request_id)["result"]
        if not isinstance(result, dict) or result.get("value") is not None:
            fail(f"closed account had a non-null value at capture: {account}")

    proof_reconstruction = reconstruct_uploaded_proof(
        decoded_transactions,
        binding,
        lifecycle,
        proof_path,
        statement_path,
    )
    program_reconstruction = reconstruct_deployed_program(
        decoded_transactions,
        binding,
        lifecycle,
        release_manifest,
        release_root,
    )

    print(
        "PASS: 2 signature pages, 1,570/1,570 full non-null finalized "
        "getTransaction responses and all member hashes; every first wire "
        "signature byte string matches its indexed transaction id; named "
        "lifecycle transactions, genesis hash, and closed account "
        "observations verified. Ed25519 signatures were not independently "
        "verified."
    )
    print(
        "PASS: reconstructed the exact "
        f"{proof_reconstruction['proof_bytes']:,}-byte proof from "
        f"{proof_reconstruction['upload_transactions']} finalized uploads; "
        f"SHA-256 {proof_reconstruction['proof_sha256']}."
    )
    print(
        "PASS: tag-67 wire and released statement bind that sealed proof "
        f"account image; sealed-account SHA-256 "
        f"{proof_reconstruction['sealed_account_sha256']}."
    )
    print(
        "PASS: reconstructed the exact "
        f"{program_reconstruction['sbf_bytes']:,}-byte SBF from "
        f"{program_reconstruction['write_transactions']:,} finalized loader writes; "
        f"{program_reconstruction['unique_write_offsets']:,} unique and "
        f"{program_reconstruction['exact_duplicate_writes']} exact retries; "
        f"SHA-256 {program_reconstruction['sbf_sha256']}."
    )
    print(
        "PASS: reconstructed the loader-v3 ProgramData image including "
        f"zero padding to max_data_len={program_reconstruction['max_data_len']:,}; "
        f"{program_reconstruction['programdata_bytes']:,} bytes, SHA-256 "
        f"{program_reconstruction['programdata_sha256']}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
