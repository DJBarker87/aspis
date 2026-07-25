#!/usr/bin/env python3
"""Offline integrity and completeness checks for the V5 mainnet RPC archive."""

from __future__ import annotations

import base64
import hashlib
import json
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
    release_checks = [
        (
            release_root / "manifest.json",
            None,
            release["manifest_sha256"],
            "mainnet release manifest",
        ),
        (
            release_root / "evidence/mainnet-lifecycle.json",
            None,
            release["lifecycle_sha256"],
            "mainnet lifecycle",
        ),
        (
            (ROOT / release["proof"]["path"]).resolve(),
            release["proof"]["bytes"],
            release["proof"]["sha256"],
            "mainnet proof",
        ),
        (
            (ROOT / release["statement"]["path"]).resolve(),
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
        signature_count, offset = read_shortvec(wire)
        if signature_count < 1 or len(wire) < offset + 64 * signature_count:
            fail(f"invalid signed transaction wire: {row['signature']}")
        if base58_encode(wire[offset : offset + 64]) != row["signature"]:
            fail(f"first wire signature mismatch: {row['signature']}")

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

    print(
        "PASS: 2 signature pages, 1,570/1,570 full non-null finalized "
        "getTransaction responses, all member hashes, all first wire "
        "signatures, named lifecycle transactions, genesis hash, and closed "
        "account observations verified."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
