#!/usr/bin/env python3
"""Archive a complete Solana address history and every full transaction response.

The output is intentionally credential-free.  The RPC URL is read from the
environment and is never written to the capture, logs, or manifest.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import hashlib
import io
import json
import os
import random
import sys
import tarfile
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


RPC_ENV = "SOLANA_RPC_URL"
PAGE_LIMIT = 1_000
RETRYABLE_RPC_CODES = {-32005, -32029, 429}
PRINT_LOCK = threading.Lock()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--address", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--provider-label", required=True)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--account", action="append", default=[])
    parser.add_argument("--max-supported-transaction-version", type=int, default=0)
    return parser.parse_args()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_json(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False).encode("utf-8")
        + b"\n"
    )


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("wb") as handle:
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def decode_response(raw: bytes, expected_id: str | int) -> dict[str, Any]:
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise RuntimeError("JSON-RPC response is not an object")
    if value.get("jsonrpc") != "2.0":
        raise RuntimeError("JSON-RPC response version is not 2.0")
    if value.get("id") != expected_id:
        raise RuntimeError("JSON-RPC response id mismatch")
    if ("result" in value) == ("error" in value):
        raise RuntimeError("JSON-RPC response must contain one result or error")
    return value


def retryable_rpc_error(response: dict[str, Any]) -> bool:
    error = response.get("error")
    return isinstance(error, dict) and error.get("code") in RETRYABLE_RPC_CODES


def call_rpc(
    rpc_url: str,
    method: str,
    params: list[Any],
    request_id: str | int,
    *,
    attempts: int = 12,
) -> bytes:
    payload = json.dumps(
        {
            "jsonrpc": "2.0",
            "id": request_id,
            "method": method,
            "params": params,
        },
        separators=(",", ":"),
    ).encode("utf-8")
    last_error: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            request = urllib.request.Request(
                rpc_url,
                data=payload,
                headers={
                    "Content-Type": "application/json",
                    "User-Agent": "aspis-evidence-archive/1",
                },
                method="POST",
            )
            with urllib.request.urlopen(request, timeout=60) as response:
                raw = response.read()
            decoded = decode_response(raw, request_id)
            if retryable_rpc_error(decoded):
                raise RuntimeError(f"retryable JSON-RPC error {decoded['error']['code']}")
            if "error" in decoded:
                raise RuntimeError(
                    "non-retryable JSON-RPC error "
                    + json.dumps(decoded["error"], sort_keys=True)
                )
            return raw
        except (TimeoutError, urllib.error.URLError, RuntimeError) as error:
            last_error = error
            if attempt == attempts:
                break
            delay = min(30.0, 0.35 * (2 ** min(attempt - 1, 6)))
            delay += random.uniform(0.0, 0.25)
            time.sleep(delay)
    raise RuntimeError(
        f"{method} failed after {attempts} attempts: {type(last_error).__name__}"
    ) from last_error


def validated_cached_response(path: Path, request_id: str | int) -> bytes | None:
    if not path.is_file():
        return None
    raw = path.read_bytes()
    try:
        response = decode_response(raw, request_id)
    except (json.JSONDecodeError, RuntimeError):
        return None
    if "error" in response:
        return None
    return raw


def archive_signature_pages(
    rpc_url: str,
    address: str,
    staging: Path,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    page_records: list[dict[str, Any]] = []
    signatures: list[dict[str, Any]] = []
    observed: set[str] = set()
    before: str | None = None
    page_number = 1

    while True:
        request_id = f"signatures-page-{page_number:04d}"
        config: dict[str, Any] = {
            "commitment": "finalized",
            "limit": PAGE_LIMIT,
        }
        if before is not None:
            config["before"] = before
        path = staging / "signature-pages" / f"page-{page_number:04d}.json"
        raw = call_rpc(
            rpc_url,
            "getSignaturesForAddress",
            [address, config],
            request_id,
        )
        atomic_write(path, raw + (b"" if raw.endswith(b"\n") else b"\n"))
        response = decode_response(raw, request_id)
        rows = response["result"]
        if not isinstance(rows, list):
            raise RuntimeError("getSignaturesForAddress result is not a list")

        for row in rows:
            signature = row.get("signature")
            if not isinstance(signature, str):
                raise RuntimeError("signature page contains an invalid signature")
            if signature in observed:
                raise RuntimeError(f"duplicate signature across pages: {signature}")
            observed.add(signature)
            signatures.append(row)

        page_records.append(
            {
                "page": page_number,
                "request_id": request_id,
                "request": {
                    "method": "getSignaturesForAddress",
                    "params": [address, config],
                },
                "response_path": str(path.relative_to(staging)),
                "response_bytes": path.stat().st_size,
                "response_sha256": sha256(path.read_bytes()),
                "result_count": len(rows),
                "newest_signature": rows[0]["signature"] if rows else None,
                "newest_slot": rows[0].get("slot") if rows else None,
                "newest_block_time": rows[0].get("blockTime") if rows else None,
                "oldest_signature": rows[-1]["signature"] if rows else None,
                "oldest_slot": rows[-1].get("slot") if rows else None,
                "oldest_block_time": rows[-1].get("blockTime") if rows else None,
                "before_for_next_page": rows[-1]["signature"] if rows else None,
            }
        )
        print(
            f"signature page {page_number}: {len(rows)} rows "
            f"(total {len(signatures)})",
            flush=True,
        )
        if len(rows) < PAGE_LIMIT:
            break
        before = rows[-1]["signature"]
        page_number += 1

    return page_records, signatures


def archive_transactions(
    rpc_url: str,
    signatures: list[dict[str, Any]],
    staging: Path,
    workers: int,
    max_supported_transaction_version: int,
) -> list[dict[str, Any]]:
    completed = 0
    total = len(signatures)

    def fetch(item: tuple[int, dict[str, Any]]) -> dict[str, Any]:
        nonlocal completed
        index, signature_record = item
        signature = signature_record["signature"]
        request_id = index
        relative_path = (
            Path("transactions") / f"{index:06d}-{signature}.json"
        )
        path = staging / relative_path
        raw = validated_cached_response(path, request_id)
        if raw is None:
            raw = call_rpc(
                rpc_url,
                "getTransaction",
                [
                    signature,
                    {
                        "commitment": "finalized",
                        "encoding": "base64",
                        "maxSupportedTransactionVersion": (
                            max_supported_transaction_version
                        ),
                    },
                ],
                request_id,
            )
            atomic_write(path, raw + (b"" if raw.endswith(b"\n") else b"\n"))
        response = decode_response(raw, request_id)
        result_present = response.get("result") is not None
        with PRINT_LOCK:
            completed += 1
            if completed == total or completed % 25 == 0:
                print(
                    f"transactions: {completed}/{total} full responses archived",
                    flush=True,
                )
        return {
            "index": index,
            "signature": signature,
            "slot": signature_record.get("slot"),
            "block_time": signature_record.get("blockTime"),
            "confirmation_status": signature_record.get("confirmationStatus"),
            "signature_error": signature_record.get("err"),
            "memo": signature_record.get("memo"),
            "response_path": str(relative_path),
            "response_bytes": path.stat().st_size,
            "response_sha256": sha256(path.read_bytes()),
            "get_transaction_result_present": result_present,
        }

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        records = list(executor.map(fetch, enumerate(signatures, start=1)))
    return records


def archive_observation(
    rpc_url: str,
    staging: Path,
    relative_path: Path,
    method: str,
    params: list[Any],
    request_id: str,
) -> dict[str, Any]:
    raw = call_rpc(rpc_url, method, params, request_id)
    path = staging / relative_path
    atomic_write(path, raw + (b"" if raw.endswith(b"\n") else b"\n"))
    response = decode_response(raw, request_id)
    return {
        "request_id": request_id,
        "request": {"method": method, "params": params},
        "response_path": str(relative_path),
        "response_bytes": path.stat().st_size,
        "response_sha256": sha256(path.read_bytes()),
        "result_present": response.get("result") is not None,
    }


def deterministic_tar_gz(staging: Path, output: Path) -> None:
    entries = sorted(path for path in staging.rglob("*") if path.is_file())
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".tmp")
    with temporary.open("wb") as raw_handle:
        with gzip.GzipFile(
            filename="",
            mode="wb",
            fileobj=raw_handle,
            mtime=0,
            compresslevel=9,
        ) as gzip_handle:
            with tarfile.open(mode="w", fileobj=gzip_handle, format=tarfile.PAX_FORMAT) as tar:
                for path in entries:
                    relative = str(path.relative_to(staging))
                    content = path.read_bytes()
                    info = tarfile.TarInfo(relative)
                    info.size = len(content)
                    info.mtime = 0
                    info.mode = 0o644
                    info.uid = 0
                    info.gid = 0
                    info.uname = ""
                    info.gname = ""
                    tar.addfile(info, io.BytesIO(content))
        raw_handle.flush()
        os.fsync(raw_handle.fileno())
    os.replace(temporary, output)


def main() -> int:
    args = parse_args()
    if args.workers < 1 or args.workers > 32:
        raise SystemExit("--workers must be in the range 1..32")
    rpc_url = os.environ.get(RPC_ENV)
    if not rpc_url:
        raise SystemExit(f"{RPC_ENV} is not set")

    output_dir = args.output_dir.resolve()
    staging = output_dir / "raw"
    staging.mkdir(parents=True, exist_ok=True)
    started_at = utc_now()

    pages, signatures = archive_signature_pages(rpc_url, args.address, staging)
    transactions = archive_transactions(
        rpc_url,
        signatures,
        staging,
        args.workers,
        args.max_supported_transaction_version,
    )

    observations: list[dict[str, Any]] = []
    observations.append(
        archive_observation(
            rpc_url,
            staging,
            Path("chain-observations/genesis-hash.json"),
            "getGenesisHash",
            [],
            "genesis-hash",
        )
    )
    observations.append(
        archive_observation(
            rpc_url,
            staging,
            Path("chain-observations/finalized-slot.json"),
            "getSlot",
            [{"commitment": "finalized"}],
            "finalized-slot",
        )
    )
    for account in args.account:
        observations.append(
            archive_observation(
                rpc_url,
                staging,
                Path("account-observations") / f"{account}.json",
                "getAccountInfo",
                [account, {"commitment": "finalized", "encoding": "base64"}],
                f"account-{account}",
            )
        )

    null_transactions = [
        row["signature"]
        for row in transactions
        if not row["get_transaction_result_present"]
    ]
    index = {
        "artifact": "solana_address_full_rpc_archive",
        "schema_version": 1,
        "capture_started_at_utc": started_at,
        "capture_completed_at_utc": utc_now(),
        "provider": args.provider_label,
        "provider_endpoint_and_credentials_published": False,
        "network_commitment": "finalized",
        "address": args.address,
        "pagination": {
            "method": "getSignaturesForAddress",
            "limit": PAGE_LIMIT,
            "cursor": "before",
            "pages": pages,
        },
        "get_transaction": {
            "method": "getTransaction",
            "encoding": "base64",
            "commitment": "finalized",
            "max_supported_transaction_version": (
                args.max_supported_transaction_version
            ),
            "response_count": len(transactions),
            "non_null_result_count": len(transactions) - len(null_transactions),
            "null_result_signatures": null_transactions,
        },
        "signature_count": len(signatures),
        "newest": transactions[0] if transactions else None,
        "oldest": transactions[-1] if transactions else None,
        "transactions": transactions,
        "observations": observations,
        "credential_safety": [
            "The RPC URL and API credential were supplied only through the process environment.",
            "Neither the endpoint nor any API credential is serialized in this archive.",
        ],
    }
    index_raw = canonical_json(index)
    atomic_write(staging / "capture-index.json", index_raw)
    atomic_write(output_dir / "index.json", index_raw)

    archive_path = output_dir / "payer-full-rpc-responses.tar.gz"
    deterministic_tar_gz(staging, archive_path)
    archive_summary = {
        "archive": archive_path.name,
        "bytes": archive_path.stat().st_size,
        "sha256": sha256(archive_path.read_bytes()),
        "members": sum(1 for path in staging.rglob("*") if path.is_file()),
        "signature_pages": len(pages),
        "signatures": len(signatures),
        "full_get_transaction_responses": len(transactions),
        "non_null_get_transaction_results": len(transactions)
        - len(null_transactions),
    }
    atomic_write(output_dir / "archive-summary.json", canonical_json(archive_summary))
    print(json.dumps(archive_summary, indent=2, sort_keys=True), flush=True)
    if null_transactions:
        print(
            f"ERROR: {len(null_transactions)} getTransaction results were null",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
