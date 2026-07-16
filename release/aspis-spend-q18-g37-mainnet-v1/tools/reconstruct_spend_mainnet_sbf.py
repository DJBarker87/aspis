#!/usr/bin/env python3
"""Reconstruct the aspis-spend mainnet SBF and tag-65 instruction from chain data.

The full upgradeable-loader write history is not checked into the repository.
Reproduction therefore requires live, archival Solana JSON-RPC endpoints unless
the caller supplies endpoints backed by an equivalent local RPC cache.  RPC
URLs remain in memory only: the result serializes fixed provider labels and no
hostname, origin, path, query string, userinfo, or other URL component.

For this run the ProgramData account was permanently closed by the finalized
cleanup transaction, so no live ProgramData snapshot exists.  The deployed
image is instead reconstructed byte-for-byte from the buffer's loader Write
history (consumed by ``deployWithMaxDataLen``), and the loader-v3 ProgramData
image is recomputed from that reconstruction and compared against the
pre-close account-data digest recorded in the committed release evidence.

The reconstruction output is deterministic except for ``captured_at_utc``.  Use
``--compare-substantive`` to compare a fresh run with a checked-in result while
ignoring only that timestamp.  The reconciliation output (``--reconciliation``)
is fully deterministic.
"""

from __future__ import annotations

import argparse
import base64
import concurrent.futures
import datetime as dt
import hashlib
import json
import pathlib
import struct
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any


SCHEMA_VERSION = 1
ARTIFACT = "spend_mainnet_sbf_and_instruction_reconstruction_v1"
RECONCILIATION_ARTIFACT = "spend_mainnet_independent_rpc_reconciliation_v1"
NETWORK = "mainnet-beta"
GENESIS_HASH = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d"

OFFICIAL_RPC = "https://api.mainnet-beta.solana.com"
INDEPENDENT_RPC = "https://solana-rpc.publicnode.com"
DEVNET_RPC = "https://api.devnet.solana.com"
TESTNET_RPC = "https://api.testnet.solana.com"
DEVNET_GENESIS = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG"
TESTNET_GENESIS = "4uhcVJyU9pJkvQyS88uRDiswHXSCkY3zQawwpjk2NsNY"

LOADER_ID = "BPFLoaderUpgradeab1e11111111111111111111111"
SYSTEM_ID = "11111111111111111111111111111111"
COMPUTE_BUDGET_ID = "ComputeBudget111111111111111111111111111111"

PROGRAM_ID = "GQPNqfYF17Nj2dGsf6Q2AtiouyM67YxFZPh9LxBk2Ye3"
PROGRAMDATA_ADDRESS = "GoXXs2juAjmpvcsX7iLdHsGJCwBwB3HHQwvYyfV3RuU"
BUFFER_ADDRESS = "BP5bCWMHQfsmsJBkTyVr1uaWudbrcbfhKEg7fmKRS4EY"
UPGRADE_AUTHORITY = "78AojysuKLSS1PeifTBy7L38rEZjgsMxsVFRagUxBpNM"
PAYER = "78u3cwKrso1yW2dwaBmMmvo8F44gvBBGfkfFay1d8HQZ"
PROOF_ACCOUNT = "59PFQsAbnM5Vjhbq7aKkxnd6MqbJ4Akw7GaDWZwAdAsk"
POOL_ADDRESS = "3ZRYarQZcWJQgzNwLo1Eo7PDmier3rbW41L8ccAddCvb"
NULLIFIER_ADDRESS = "CFJ5fYPSi4Qn6okBCZS3tXFMw7Lsz4Jy9vEAAGU5kfSU"

DEPLOYMENT_SIGNATURE = (
    "qdeDmK712P3ifnn4hfqtEH3CzW7rssoP9hsJtCceebmAnA5qSrN34v4KE1H6tJbWbUjD7GdaZmLv2CxV823coW8"
)
BUFFER_INITIALIZE_SIGNATURE = (
    "5HSfC4QsRJZy9uzobRJmiQoDy7RCtR19Ukdo6NTfqapnwNKXCgCEmKPxUxx8prxoohFZLQxYU3gCiroM1Ppy7RBE"
)
VERIFICATION_SIGNATURE = (
    "3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv"
)
PROGRAMDATA_CLOSE_SIGNATURE = (
    "3mfD5KEYXJ4ZyC2XeHW4fXKNYUqo46SA1waGeJ3CNz7fBzzxqy4rK6tiniVpx5D4ZpDziCEKgi66KUdEjyLkrVDo"
)

DEPLOYMENT_SLOT = 433_219_270
DEPLOYMENT_BLOCK_TIME = 1_784_182_962
BUFFER_INITIALIZE_SLOT = 433_219_157
VERIFICATION_SLOT = 433_219_840
VERIFICATION_BLOCK_TIME = 1_784_183_193
PROGRAMDATA_CLOSE_SLOT = 433_220_251
PROGRAMDATA_CLOSE_BLOCK_TIME = 1_784_183_366

SBF_BYTES = 924_344
SBF_SHA256 = "e289faf85fe4773880794d5d4356461bb9cb94077b68711f99348efe19707d7e"
# The ProgramData account is CLOSED. This digest is recomputed from the
# reconstructed image and cross-checked against the pre-close account-data
# digest recorded in the committed release evidence; it is not from a live snap.
PROGRAMDATA_BYTES = 924_389
PROGRAMDATA_SHA256 = "708c5e5e171942b7b93df4188a564681fe49e476902014e634734b04ad8ade83"
PROGRAMDATA_HEADER_HEX = (
    "03000000c666d21900000000015afc46570a0cc7b5bdfff16323f545"
    "00f18eb187ad8d6fdadb5450fe2c004c92"
)

PROOF_BYTES = 65_407
PROOF_SHA256 = "32eb419e0c5c3ef4fa2db0d32579e88f1207547d8fb010279efeb6c05981b529"
DEPLOYMENT_DOMAIN_HEX = (
    "ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f"
)
TAG65_PAYLOAD_BYTES = 169
TAG65_PAYLOAD_SHA256 = "c02a5916d0b8b70a7599d4e37c80c61e7de06fa26e2098cab23e1ba5dd2cfc3d"
TAG65_PAYLOAD_HEX = (
    "4190bc3005a8029b06072f386dc6b1ee4e9b4ba513b126d033a96ecc49829cab5a"
    "890266278df8f3073cab562c6c7d89471363c46841748a1ef3b0432acd0afd5f"
    "69517012bd98fe78bef9b076069520614ef27f2fc7a0854f72e65055a2edc319"
    "9f5b8c2dc991e401f3538941af35fd29e00aa319edca8013c7260c61c2e7486e"
    "1100000001000000"
    "ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f"
)

# Loader-write shape observed for this run: 1069 full 864-byte writes plus one
# final 728-byte write, for 1070 writes total. Buffer history newest-to-oldest
# is [deploy, 1070 writes, buffer initialize] = 1072 records.
HISTORY_COUNT = 1_072
WRITE_COUNT = 1_070
FULL_CHUNK_BYTES = 864
FULL_CHUNK_COUNT = 1_069
FINAL_CHUNK_OFFSET = 923_616
FINAL_CHUNK_BYTES = 728
BUFFER_SPACE = 924_381
BUFFER_LAMPORTS = 6_434_638_320
PROGRAMDATA_REFUND_LAMPORTS = 6_434_638_320
PAGE_SIZES_BEFORE_DEPLOYMENT = [1000, 71]

BASE58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
BASE58_INDEX = {character: index for index, character in enumerate(BASE58_ALPHABET)}


class ReconstructionError(RuntimeError):
    """A fail-closed validation or RPC error safe to print."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReconstructionError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def canonical_json_sha256(value: Any) -> str:
    return sha256_bytes(canonical_json_bytes(value))


def normalized_json_sha256(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return sha256_bytes(encoded)


def base58_decode(value: str) -> bytes:
    number = 0
    try:
        for character in value:
            number = number * 58 + BASE58_INDEX[character]
    except KeyError as error:
        raise ReconstructionError("invalid base58 data returned by RPC") from error
    decoded = number.to_bytes((number.bit_length() + 7) // 8, "big") if number else b""
    return b"\x00" * (len(value) - len(value.lstrip("1"))) + decoded


def sanitized_origin(url: str) -> str:
    try:
        parts = urllib.parse.urlsplit(url)
        port = parts.port
    except ValueError as error:
        raise ReconstructionError("RPC URL has an invalid port") from error
    require(parts.scheme in {"http", "https"}, "RPC URL must use HTTP or HTTPS")
    require(parts.hostname is not None, "RPC URL must contain a hostname")
    hostname = parts.hostname
    if ":" in hostname and not hostname.startswith("["):
        hostname = f"[{hostname}]"
    netloc = hostname if port is None else f"{hostname}:{port}"
    return urllib.parse.urlunsplit((parts.scheme, netloc, "", "", ""))


class RpcClient:
    def __init__(
        self,
        label: str,
        url: str,
        timeout: float,
        retries: int,
        requests_per_second: float,
    ) -> None:
        self.label = label
        self.url = url
        self.origin = sanitized_origin(url)
        self.timeout = timeout
        self.retries = retries
        self.requests_per_second = requests_per_second
        self._rate_lock = threading.Lock()
        self._next_request_at = 0.0
        self._cooldown_until = 0.0

    def _wait_for_rate_slot(self) -> None:
        while True:
            with self._rate_lock:
                now = time.monotonic()
                if now < self._cooldown_until:
                    target = self._cooldown_until
                    reserved_rate_slot = False
                elif self.requests_per_second > 0:
                    target = max(now, self._next_request_at)
                    self._next_request_at = target + 1.0 / self.requests_per_second
                    reserved_rate_slot = True
                else:
                    return
            delay = target - now
            if delay > 0:
                time.sleep(delay)
            if not reserved_rate_slot:
                continue
            with self._rate_lock:
                if time.monotonic() < self._cooldown_until:
                    continue
            return

    def _impose_client_wide_cooldown(self, seconds: float) -> None:
        with self._rate_lock:
            cooldown_until = time.monotonic() + max(0.0, seconds)
            self._cooldown_until = max(self._cooldown_until, cooldown_until)
            self._next_request_at = max(self._next_request_at, self._cooldown_until)

    @staticmethod
    def _http_retry_after(error: urllib.error.HTTPError) -> float:
        raw_value = (
            error.headers.get("Retry-After") if error.headers is not None else None
        )
        if raw_value is not None:
            try:
                value = float(raw_value)
                if value >= 0:
                    return value
            except ValueError:
                pass
        return 10.0

    def call(self, method: str, params: list[Any]) -> Any:
        payload = canonical_json_bytes(
            {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
        )
        for attempt in range(self.retries):
            self._wait_for_rate_slot()
            try:
                request = urllib.request.Request(
                    self.url,
                    data=payload,
                    headers={
                        "content-type": "application/json",
                        "user-agent": "aspis-spend-reconstruction/1",
                    },
                )
                with urllib.request.urlopen(request, timeout=self.timeout) as response:
                    decoded = json.load(response)
            except urllib.error.HTTPError as error:
                if error.code == 429 and attempt + 1 < self.retries:
                    retry_after = self._http_retry_after(error)
                    self._impose_client_wide_cooldown(retry_after)
                    error.close()
                    continue
                error.close()
                raise ReconstructionError(
                    f"{self.label} returned HTTP {error.code} for {method}"
                ) from None
            except (urllib.error.URLError, TimeoutError, json.JSONDecodeError):
                if attempt + 1 < self.retries:
                    time.sleep(min(10.0, 0.3 * (2 ** min(attempt, 5))))
                    continue
                raise ReconstructionError(
                    f"{self.label} failed while calling {method}"
                ) from None

            require(
                isinstance(decoded, dict),
                f"{self.label} returned a non-object RPC response",
            )
            error_object = decoded.get("error")
            if error_object is not None:
                code = (
                    error_object.get("code") if isinstance(error_object, dict) else None
                )
                if code == 429 and attempt + 1 < self.retries:
                    self._impose_client_wide_cooldown(10.0)
                    continue
                raise ReconstructionError(
                    f"{self.label} returned JSON-RPC error code {code!r} for {method}"
                )
            require(
                "result" in decoded, f"{self.label} omitted the RPC result for {method}"
            )
            return decoded["result"]
        raise ReconstructionError(f"{self.label} exhausted retries for {method}")


def fetch_predeployment_history(
    client: RpcClient,
) -> tuple[list[dict[str, Any]], list[int]]:
    all_records: list[dict[str, Any]] = []
    page_sizes: list[int] = []
    before: str | None = DEPLOYMENT_SIGNATURE
    found_initialize = False
    for _ in range(20):
        config: dict[str, Any] = {"limit": 1000, "commitment": "finalized"}
        if before is not None:
            config["before"] = before
        page = client.call("getSignaturesForAddress", [BUFFER_ADDRESS, config])
        require(
            isinstance(page, list),
            f"{client.label} returned invalid signature history",
        )
        page_sizes.append(len(page))
        all_records.extend(page)
        if any(
            isinstance(record, dict)
            and record.get("signature") == BUFFER_INITIALIZE_SIGNATURE
            for record in page
        ):
            found_initialize = True
            break
        require(
            len(page) == 1000,
            f"{client.label} history ended before buffer initialization",
        )
        before = page[-1].get("signature") if page else None
        require(isinstance(before, str), f"{client.label} returned an invalid cursor")
    require(found_initialize, f"{client.label} did not return the buffer initialization")

    signatures = [record.get("signature") for record in all_records]
    require(
        all(isinstance(signature, str) for signature in signatures),
        "history contains a bad signature",
    )
    require(len(signatures) == len(set(signatures)), "history contains duplicates")
    try:
        end = signatures.index(BUFFER_INITIALIZE_SIGNATURE) + 1
    except ValueError as error:
        raise ReconstructionError(
            "history does not reach the buffer initialization"
        ) from error
    selected = all_records[:end]
    require(
        all(record.get("signature") != DEPLOYMENT_SIGNATURE for record in selected),
        "before=deployment pagination unexpectedly included deployment",
    )
    return selected, page_sizes


def raw_transaction(client: RpcClient, signature: str) -> dict[str, Any]:
    transaction = client.call(
        "getTransaction",
        [
            signature,
            {
                "encoding": "json",
                "commitment": "finalized",
                "maxSupportedTransactionVersion": 0,
            },
        ],
    )
    require(
        isinstance(transaction, dict),
        f"{client.label} returned no transaction for a pinned signature",
    )
    return transaction


def parsed_transaction(client: RpcClient, signature: str) -> dict[str, Any]:
    transaction = client.call(
        "getTransaction",
        [
            signature,
            {
                "encoding": "jsonParsed",
                "commitment": "finalized",
                "maxSupportedTransactionVersion": 0,
            },
        ],
    )
    require(
        isinstance(transaction, dict), f"{client.label} returned no parsed transaction"
    )
    return transaction


def account_keys(message: dict[str, Any]) -> list[str]:
    raw_keys = message.get("accountKeys")
    require(isinstance(raw_keys, list), "transaction message has no account keys")
    keys: list[str] = []
    for entry in raw_keys:
        if isinstance(entry, str):
            keys.append(entry)
        elif isinstance(entry, dict) and isinstance(entry.get("pubkey"), str):
            keys.append(entry["pubkey"])
        else:
            raise ReconstructionError("transaction message contains an invalid key")
    return keys


def instruction_program_id(instruction: dict[str, Any], keys: list[str]) -> str:
    direct = instruction.get("programId")
    if isinstance(direct, str):
        return direct
    index = instruction.get("programIdIndex")
    require(
        isinstance(index, int) and 0 <= index < len(keys),
        "instruction has a bad program id index",
    )
    return keys[index]


def transaction_message(transaction: dict[str, Any]) -> dict[str, Any]:
    envelope = transaction.get("transaction")
    require(isinstance(envelope, dict), "RPC transaction envelope is missing")
    message = envelope.get("message")
    require(isinstance(message, dict), "RPC transaction message is missing")
    return message


def transaction_meta(transaction: dict[str, Any]) -> dict[str, Any]:
    meta = transaction.get("meta")
    require(isinstance(meta, dict), "RPC transaction metadata is missing")
    return meta


def validate_envelope_signatures(
    transaction: dict[str, Any], expected_first: str, expected_count: int
) -> list[str]:
    envelope = transaction.get("transaction")
    require(isinstance(envelope, dict), "RPC transaction envelope is missing")
    signatures = envelope.get("signatures")
    require(
        isinstance(signatures, list) and len(signatures) == expected_count,
        "transaction signature count mismatch",
    )
    require(signatures[0] == expected_first, "first envelope signature is not the id")
    require(len(set(signatures)) == expected_count, "duplicate transaction signatures")
    for signature in signatures:
        require(isinstance(signature, str), "transaction contains a non-string signature")
        require(len(base58_decode(signature)) == 64, "transaction signature not 64 bytes")
    return signatures


def parsed_instruction(
    transaction: dict[str, Any], expected_type: str, expected_program: str
) -> dict[str, Any]:
    message = transaction_message(transaction)
    instructions = message.get("instructions")
    require(isinstance(instructions, list), "parsed transaction has no instructions")
    matches = []
    for instruction in instructions:
        if (
            not isinstance(instruction, dict)
            or instruction.get("program") != expected_program
        ):
            continue
        parsed = instruction.get("parsed")
        if isinstance(parsed, dict) and parsed.get("type") == expected_type:
            matches.append(parsed.get("info"))
    require(
        len(matches) == 1 and isinstance(matches[0], dict),
        f"missing parsed {expected_type} instruction",
    )
    return matches[0]


def validate_deployment(
    official: RpcClient, independent: RpcClient
) -> tuple[dict[str, Any], dict[str, Any]]:
    provider_values: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for client in (official, independent):
        deployment = parsed_transaction(client, DEPLOYMENT_SIGNATURE)
        require(deployment.get("slot") == DEPLOYMENT_SLOT, "deployment slot mismatch")
        require(
            deployment.get("blockTime") == DEPLOYMENT_BLOCK_TIME,
            "deployment block time mismatch",
        )
        require(
            transaction_meta(deployment).get("err") is None,
            "deployment transaction failed",
        )
        deploy_info = parsed_instruction(
            deployment, "deployWithMaxDataLen", "bpf-upgradeable-loader"
        )

        initialization = parsed_transaction(client, BUFFER_INITIALIZE_SIGNATURE)
        require(
            transaction_meta(initialization).get("err") is None,
            "buffer initialization failed",
        )
        create_info = parsed_instruction(initialization, "createAccount", "system")
        initialize_info = parsed_instruction(
            initialization, "initializeBuffer", "bpf-upgradeable-loader"
        )
        provider_values.append(
            (
                {
                    "slot": deployment.get("slot"),
                    "block_time_unix": deployment.get("blockTime"),
                    "info": deploy_info,
                },
                {"create": create_info, "initialize": initialize_info},
            )
        )
    require(
        provider_values[0] == provider_values[1],
        "providers disagree on deployment identities",
    )
    deploy, initialization = provider_values[0]
    info = deploy["info"]
    require(info.get("authority") == UPGRADE_AUTHORITY, "deployment authority mismatch")
    require(info.get("bufferAccount") == BUFFER_ADDRESS, "deployment buffer mismatch")
    require(info.get("maxDataLen") == SBF_BYTES, "deployment max data length mismatch")
    require(info.get("payerAccount") == PAYER, "deployment payer mismatch")
    require(info.get("programAccount") == PROGRAM_ID, "deployment program id mismatch")
    require(
        info.get("programDataAccount") == PROGRAMDATA_ADDRESS,
        "deployment ProgramData mismatch",
    )
    require(info.get("systemProgram") == SYSTEM_ID, "deployment system program mismatch")

    create = initialization["create"]
    initialize = initialization["initialize"]
    require(create.get("newAccount") == BUFFER_ADDRESS, "buffer create address mismatch")
    require(create.get("owner") == LOADER_ID, "buffer owner mismatch")
    require(create.get("source") == PAYER, "buffer funding source mismatch")
    require(create.get("space") == BUFFER_SPACE, "buffer space mismatch")
    require(create.get("lamports") == BUFFER_LAMPORTS, "buffer rent mismatch")
    require(initialize.get("account") == BUFFER_ADDRESS, "initialized buffer mismatch")
    require(
        initialize.get("authority") == UPGRADE_AUTHORITY, "buffer authority mismatch"
    )
    return deploy, initialization


def fetch_history_transactions(
    history: list[dict[str, Any]], transaction_client: RpcClient, workers: int
) -> list[dict[str, Any]]:
    signatures = [record["signature"] for record in history]

    def fetch(pair: tuple[int, str]) -> tuple[int, dict[str, Any]]:
        index, signature = pair
        return index, raw_transaction(transaction_client, signature)

    transactions: dict[int, dict[str, Any]] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        futures = [executor.submit(fetch, pair) for pair in enumerate(signatures)]
        for completed, future in enumerate(
            concurrent.futures.as_completed(futures), start=1
        ):
            index, transaction = future.result()
            transactions[index] = transaction
            if completed % 100 == 0 or completed == len(signatures):
                print(
                    f"{transaction_client.label}: fetched "
                    f"{completed}/{len(signatures)} transactions",
                    file=sys.stderr,
                    flush=True,
                )
    require(
        len(transactions) == len(signatures),
        "not every history transaction was fetched",
    )
    return [transactions[index] for index in range(len(signatures))]


def reconstruct_sbf(
    history: list[dict[str, Any]], transactions: list[dict[str, Any]]
) -> tuple[bytes, dict[str, Any]]:
    signatures = [record["signature"] for record in history]
    require(len(transactions) == len(signatures), "history/transaction count mismatch")

    image = bytearray(SBF_BYTES)
    covered = bytearray(SBF_BYTES)
    write_count = 0
    payload_sum = 0
    overlap_bytes = 0
    conflicting_overlap_bytes = 0
    out_of_bounds_writes = 0
    chunks: list[tuple[int, int]] = []

    for index, signature in enumerate(signatures):
        transaction = transactions[index]
        require(
            transaction.get("slot") == history[index].get("slot"),
            "transaction slot changed",
        )
        meta = transaction_meta(transaction)
        require(meta.get("err") is None, "a buffer-history transaction failed")
        message = transaction_message(transaction)
        keys = account_keys(message)
        instructions = message.get("instructions")
        require(isinstance(instructions, list), "transaction instruction list absent")
        transaction_write_count = 0
        for instruction in instructions:
            require(isinstance(instruction, dict), "invalid transaction instruction")
            if instruction_program_id(instruction, keys) != LOADER_ID:
                continue
            encoded = instruction.get("data")
            require(isinstance(encoded, str), "loader instruction data is absent")
            raw = base58_decode(encoded)
            if len(raw) < 4 or struct.unpack_from("<I", raw)[0] != 1:
                # Not a loader Write (initializeBuffer / deployWithMaxDataLen).
                continue
            transaction_write_count += 1
            validate_envelope_signatures(transaction, signature, 2)
            require(transaction.get("version") == "legacy", "write tx is not legacy")
            header = message.get("header")
            require(
                header
                == {
                    "numRequiredSignatures": 2,
                    "numReadonlySignedAccounts": 1,
                    "numReadonlyUnsignedAccounts": 2,
                },
                "loader write message header mismatch",
            )
            require(
                keys == [PAYER, UPGRADE_AUTHORITY, BUFFER_ADDRESS, LOADER_ID,
                         COMPUTE_BUDGET_ID],
                "loader write static account-key order mismatch",
            )
            unsigned_writable_end = len(keys) - header["numReadonlyUnsignedAccounts"]
            require(
                header["numRequiredSignatures"] <= 2 < unsigned_writable_end,
                "write buffer is not an unsigned writable account",
            )
            require(
                instruction.get("programIdIndex") == 3,
                "loader write program index mismatch",
            )
            require(
                instruction.get("accounts") == [2, 1],
                "loader write account indices mismatch",
            )
            require(
                instruction.get("stackHeight") in (None, 1),
                "loader write stack height mismatch",
            )
            require(len(raw) >= 16, "loader write instruction is truncated")
            variant, offset, payload_length = struct.unpack_from("<IIQ", raw)
            require(variant == 1, "unexpected loader write variant")
            payload = raw[16:]
            require(len(payload) == payload_length, "loader write payload length mismatch")
            if offset + payload_length > SBF_BYTES:
                out_of_bounds_writes += 1
                continue
            for image_index, value in enumerate(payload, offset):
                if covered[image_index]:
                    overlap_bytes += 1
                    if image[image_index] != value:
                        conflicting_overlap_bytes += 1
                image[image_index] = value
                covered[image_index] = 1
            write_count += 1
            payload_sum += payload_length
            chunks.append((offset, payload_length))
        expected_transaction_writes = 1 if 0 < index < len(signatures) - 1 else 0
        require(
            transaction_write_count == expected_transaction_writes,
            "history transaction has an unexpected loader Write count",
        )

    unique_covered = sum(covered)
    gap_bytes = covered.count(0)
    require(write_count == WRITE_COUNT, "loader write count mismatch")
    require(out_of_bounds_writes == 0, "loader history contains an out-of-bounds write")
    require(overlap_bytes == 0, "loader history contains overlapping writes")
    require(conflicting_overlap_bytes == 0, "loader history contains conflicting writes")
    require(payload_sum == SBF_BYTES, "loader payload byte sum mismatch")
    require(
        unique_covered == SBF_BYTES and gap_bytes == 0,
        "loader history does not cover the SBF",
    )
    require(
        sum(length == FULL_CHUNK_BYTES for _, length in chunks) == FULL_CHUNK_COUNT,
        "full write chunk count mismatch",
    )
    require(
        sorted(chunks)[-1] == (FINAL_CHUNK_OFFSET, FINAL_CHUNK_BYTES),
        "final loader chunk mismatch",
    )
    require(sha256_bytes(bytes(image)) == SBF_SHA256, "reconstructed SBF hash mismatch")
    return bytes(image), {
        "history_transaction_count": len(transactions),
        "history_transactions_meta_err_null": True,
        "write_accounts_exact": True,
        "write_message_header_exact": True,
        "write_static_account_keys_exact": True,
        "write_signatures_exact": True,
        "write_authority_required_signer": True,
        "write_buffer_writable": True,
        "write_transactions_legacy": True,
        "loader_write_variant_u32_le": 1,
        "loader_write_encoding": (
            "u32_le variant || u32_le offset || u64_le payload_len || payload"
        ),
        "write_instruction_count": write_count,
        "full_chunk_count": FULL_CHUNK_COUNT,
        "full_chunk_bytes": FULL_CHUNK_BYTES,
        "final_chunk_offset": FINAL_CHUNK_OFFSET,
        "final_chunk_bytes": FINAL_CHUNK_BYTES,
        "sum_payload_bytes": payload_sum,
        "unique_covered_bytes": unique_covered,
        "gap_bytes": gap_bytes,
        "overlap_bytes": overlap_bytes,
        "conflicting_overlap_bytes": conflicting_overlap_bytes,
        "out_of_bounds_writes": out_of_bounds_writes,
        "reconstructed_sbf_bytes": len(image),
        "reconstructed_sbf_sha256": sha256_bytes(bytes(image)),
    }


def signature_status(client: RpcClient, signature: str) -> dict[str, Any]:
    result = client.call(
        "getSignatureStatuses", [[signature], {"searchTransactionHistory": True}]
    )
    require(isinstance(result, dict), "signature-status response is malformed")
    values = result.get("value")
    require(
        isinstance(values, list) and len(values) == 1,
        "signature status is absent",
    )
    status = values[0]
    if status is None:
        return {"present": False, "slot": None, "confirmation_status": None, "err": None}
    require(isinstance(status, dict), "signature status is malformed")
    return {
        "present": True,
        "slot": status.get("slot"),
        "confirmation_status": status.get("confirmationStatus"),
        "err": status.get("err"),
    }


def verified_deployment_record(
    client: RpcClient,
) -> tuple[dict[str, Any], dict[str, Any]]:
    transaction = raw_transaction(client, DEPLOYMENT_SIGNATURE)
    require(transaction.get("slot") == DEPLOYMENT_SLOT, "deployment slot mismatch")
    require(
        transaction.get("blockTime") == DEPLOYMENT_BLOCK_TIME,
        "deployment block time mismatch",
    )
    require(
        transaction_meta(transaction).get("err") is None, "deployment transaction failed"
    )
    validate_envelope_signatures(transaction, DEPLOYMENT_SIGNATURE, 3)
    status = signature_status(client, DEPLOYMENT_SIGNATURE)
    require(status["slot"] == DEPLOYMENT_SLOT, "deployment status slot mismatch")
    require(status["confirmation_status"] == "finalized", "deployment not finalized")
    require(status["err"] is None, "deployment status records an error")
    return (
        {
            "signature": DEPLOYMENT_SIGNATURE,
            "slot": DEPLOYMENT_SLOT,
            "blockTime": DEPLOYMENT_BLOCK_TIME,
            "err": None,
            "confirmationStatus": "finalized",
        },
        transaction,
    )


def instruction_account_pubkeys(
    instruction: dict[str, Any], keys: list[str]
) -> list[str]:
    raw_accounts = instruction.get("accounts")
    require(isinstance(raw_accounts, list), "instruction accounts are absent")
    resolved: list[str] = []
    for account in raw_accounts:
        if isinstance(account, int):
            require(0 <= account < len(keys), "instruction account index is invalid")
            resolved.append(keys[account])
        elif isinstance(account, str):
            resolved.append(account)
        else:
            raise ReconstructionError("instruction account entry is invalid")
    return resolved


def parse_tag65(transaction: dict[str, Any]) -> dict[str, Any]:
    require(transaction.get("slot") == VERIFICATION_SLOT, "verification slot mismatch")
    require(
        transaction.get("blockTime") == VERIFICATION_BLOCK_TIME,
        "verification block time mismatch",
    )
    meta = transaction_meta(transaction)
    require(meta.get("err") is None, "verification transaction failed")
    require(meta.get("fee") == 10_000, "verification fee mismatch")
    require(
        meta.get("computeUnitsConsumed") == 1_344_003, "verification CU mismatch"
    )

    envelope_signatures = validate_envelope_signatures(
        transaction, VERIFICATION_SIGNATURE, 2
    )
    require(transaction.get("version") == "legacy", "verification tx is not legacy")
    message = transaction_message(transaction)
    keys = account_keys(message)
    require(
        message.get("header")
        == {
            "numRequiredSignatures": 2,
            "numReadonlySignedAccounts": 0,
            "numReadonlyUnsignedAccounts": 3,
        },
        "verification message header mismatch",
    )
    require(
        keys
        == [PAYER, PROOF_ACCOUNT, POOL_ADDRESS, NULLIFIER_ADDRESS, SYSTEM_ID,
            COMPUTE_BUDGET_ID, PROGRAM_ID],
        "verification static account-key order mismatch",
    )
    instructions = message.get("instructions")
    require(isinstance(instructions, list), "verification instructions are absent")
    require(len(instructions) == 3, "verification instruction count mismatch")
    require(
        all(
            isinstance(instructions[index], dict)
            and instruction_program_id(instructions[index], keys) == COMPUTE_BUDGET_ID
            for index in (0, 1)
        ),
        "verification compute-budget instruction order mismatch",
    )
    matches: list[tuple[int, dict[str, Any]]] = []
    for index, instruction in enumerate(instructions):
        require(isinstance(instruction, dict), "verification has an invalid instruction")
        if instruction_program_id(instruction, keys) == PROGRAM_ID:
            matches.append((index, instruction))
    require(len(matches) == 1, "verification must contain one application instruction")
    instruction_index, instruction = matches[0]
    require(instruction_index == 2, "tag65 is not the third message instruction")
    require(instruction.get("programIdIndex") == 6, "tag65 program index mismatch")
    require(instruction.get("accounts") == [1, 2, 3, 0, 4], "tag65 account indices mismatch")
    require(instruction.get("stackHeight") in (None, 1), "tag65 stack height mismatch")
    encoded = instruction.get("data")
    require(isinstance(encoded, str), "tag65 instruction data is absent")
    payload = base58_decode(encoded)
    require(len(payload) == TAG65_PAYLOAD_BYTES, "tag65 payload length mismatch")
    require(sha256_bytes(payload) == TAG65_PAYLOAD_SHA256, "tag65 payload hash mismatch")
    require(payload.hex() == TAG65_PAYLOAD_HEX, "tag65 payload bytes mismatch")

    instruction_accounts = instruction_account_pubkeys(instruction, keys)
    expected_accounts = [PROOF_ACCOUNT, POOL_ADDRESS, NULLIFIER_ADDRESS, PAYER, SYSTEM_ID]
    require(instruction_accounts == expected_accounts, "tag65 account order mismatch")

    tag = payload[0]
    current_anchor = payload[1:33].hex()
    nullifier = payload[33:65].hex()
    output_commitment = payload[65:97].hex()
    output_anchor = payload[97:129].hex()
    asset_id = struct.unpack_from("<I", payload, 129)[0]
    fee = struct.unpack_from("<I", payload, 133)[0]
    deployment_domain = payload[137:169].hex()
    decoded = {
        "tag": tag,
        "current_anchor_hex": current_anchor,
        "nullifier_hex": nullifier,
        "output_commitment_hex": output_commitment,
        "output_anchor_hex": output_anchor,
        "asset_id_u32_le": asset_id,
        "fee_u32_le": fee,
        "deployment_domain_hex": deployment_domain,
    }
    require(
        decoded
        == {
            "tag": 65,
            "current_anchor_hex": "90bc3005a8029b06072f386dc6b1ee4e9b4ba513b126d033a96ecc49829cab5a",
            "nullifier_hex": "890266278df8f3073cab562c6c7d89471363c46841748a1ef3b0432acd0afd5f",
            "output_commitment_hex": "69517012bd98fe78bef9b076069520614ef27f2fc7a0854f72e65055a2edc319",
            "output_anchor_hex": "9f5b8c2dc991e401f3538941af35fd29e00aa319edca8013c7260c61c2e7486e",
            "asset_id_u32_le": 17,
            "fee_u32_le": 1,
            "deployment_domain_hex": DEPLOYMENT_DOMAIN_HEX,
        },
        "decoded tag65 fields mismatch",
    )

    log_messages = meta.get("logMessages")
    require(isinstance(log_messages, list), "verification log messages are absent")
    invoke_log = f"Program {PROGRAM_ID} invoke [1]"
    success_log = f"Program {PROGRAM_ID} success"
    invoke_positions = [i for i, line in enumerate(log_messages) if line == invoke_log]
    success_positions = [i for i, line in enumerate(log_messages) if line == success_log]
    require(
        len(invoke_positions) == 1
        and len(success_positions) == 1
        and invoke_positions[0] < success_positions[0],
        "verification program invocation/success segment is malformed",
    )
    segment = log_messages[invoke_positions[0] + 1 : success_positions[0]]
    segment_data_logs = [
        line
        for line in segment
        if isinstance(line, str) and line.startswith("Program data: ")
    ]
    all_data_logs = [
        line
        for line in log_messages
        if isinstance(line, str) and line.startswith("Program data: ")
    ]
    require(
        len(segment_data_logs) == 1 and all_data_logs == segment_data_logs,
        "proof-digest log is not uniquely inside the program invocation segment",
    )
    proof_data_log = segment_data_logs[0]
    pieces = proof_data_log.split()
    require(len(pieces) == 4, "verification proof-digest log is malformed")
    try:
        domain = base64.b64decode(pieces[2], validate=True).decode("ascii")
        logged_digest = base64.b64decode(pieces[3], validate=True).hex()
    except (ValueError, UnicodeDecodeError) as error:
        raise ReconstructionError(
            "verification proof-digest log is not valid base64"
        ) from error
    require(domain == "aspis-proof-sha256-v1", "verification proof-log domain mismatch")
    require(logged_digest == PROOF_SHA256, "verification proof-log digest mismatch")

    pre_balances = meta.get("preBalances")
    post_balances = meta.get("postBalances")
    require(
        isinstance(pre_balances, list) and isinstance(post_balances, list),
        "verification balances are absent",
    )
    require(
        len(pre_balances) == len(keys) == len(post_balances) == 7,
        "verification balance-vector length mismatch",
    )
    require(
        pre_balances == [295_286_560, 456_402_000, 1_447_680, 0, 1, 1, 1_141_440],
        "verification pre-balances mismatch",
    )
    require(
        post_balances == [750_286_560, 0, 1_447_680, 1_392_000, 1, 1, 1_141_440],
        "verification post-balances mismatch",
    )
    # payer(0) + fee + nullifier(3) == payer_pre(0) + proof_pre(1); pool(2) unchanged.
    refund_equation = (
        post_balances[0] + meta["fee"] + post_balances[3]
        == pre_balances[0] + pre_balances[1]
    )
    require(refund_equation, "verification proof-refund equation failed")
    require(pre_balances[2] == post_balances[2], "verification pool balance changed")

    return {
        "signature": VERIFICATION_SIGNATURE,
        "slot": transaction["slot"],
        "block_time_unix": transaction["blockTime"],
        "meta_err": None,
        "program_id": PROGRAM_ID,
        "transaction_version": "legacy",
        "message_header": message["header"],
        "static_account_keys": keys,
        "envelope_signature_count": len(envelope_signatures),
        "envelope_signatures_valid_base58_64_bytes": True,
        "message_instruction_index_zero_based": instruction_index,
        "accounts_in_instruction_order": instruction_accounts,
        "payload_bytes": len(payload),
        "payload_sha256": sha256_bytes(payload),
        "payload_hex": payload.hex(),
        "decoded": decoded,
        "proof_log": {
            "domain": domain,
            "proof_sha256": logged_digest,
            "raw_log_line": proof_data_log,
            "inside_program_invocation_success_segment": True,
            "program_success_log": success_log,
        },
        "compute_units_consumed": meta["computeUnitsConsumed"],
        "fee_lamports": meta["fee"],
        "refund": {
            "account_indices": {
                "payer": 0,
                "proof": 1,
                "pool": 2,
                "nullifier": 3,
            },
            "payer_pre_lamports": pre_balances[0],
            "proof_pre_lamports": pre_balances[1],
            "nullifier_pre_lamports": pre_balances[3],
            "payer_post_lamports": post_balances[0],
            "proof_post_lamports": post_balances[1],
            "nullifier_post_lamports": post_balances[3],
            "proof_refund_lamports": pre_balances[1] - post_balances[1],
            "pool_balance_unchanged": pre_balances[2] == post_balances[2],
            "exact_balance_equation_recomputed": refund_equation,
        },
    }


def load_json(path: pathlib.Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReconstructionError(
            f"cannot read checked-in evidence: {path.name}"
        ) from error
    require(isinstance(value, dict), f"checked-in evidence is not an object: {path.name}")
    return value


def validate_checked_in_evidence(repo_root: pathlib.Path) -> dict[str, Any]:
    execution_path = (
        repo_root
        / "release/aspis-spend-q18-g37-mainnet-v1/evidence/mainnet-execution.json"
    )
    cleanup_path = (
        repo_root
        / "release/aspis-spend-q18-g37-mainnet-v1/evidence/mainnet-cleanup.json"
    )
    execution = load_json(execution_path)
    cleanup = load_json(cleanup_path)

    require(
        execution.get("artifact") == "spend_mainnet_beta_finalized_demo",
        "execution evidence artifact mismatch",
    )
    require(execution.get("program_id") == PROGRAM_ID, "execution program id mismatch")
    require(execution.get("sbf_sha256") == SBF_SHA256, "execution SBF hash mismatch")
    require(execution.get("proof_sha256") == PROOF_SHA256, "execution proof hash mismatch")

    ft = execution.get("final_transaction", {})
    require(ft.get("signature") == VERIFICATION_SIGNATURE, "execution tag65 sig mismatch")
    require(ft.get("finalized_slot") == VERIFICATION_SLOT, "execution tag65 slot mismatch")
    require(
        ft.get("compute_units_consumed") == 1_344_003, "execution tag65 CU mismatch"
    )

    # Pre-close ProgramData image, recorded before the account was closed.
    pd = execution.get("upgradeable_program_after_finality", {}).get(
        "programdata_account", {}
    )
    require(pd.get("data_len") == PROGRAMDATA_BYTES, "recorded ProgramData length mismatch")
    require(
        pd.get("data_sha256") == PROGRAMDATA_SHA256, "recorded ProgramData hash mismatch"
    )
    require(
        execution.get("upgradeable_program_after_finality", {}).get("programdata_slot")
        == DEPLOYMENT_SLOT,
        "recorded ProgramData slot mismatch",
    )
    require(
        execution.get("upgradeable_program_after_finality", {}).get(
            "upgrade_authority_address"
        )
        == UPGRADE_AUTHORITY,
        "recorded authority mismatch",
    )

    require(
        cleanup.get("signature") == PROGRAMDATA_CLOSE_SIGNATURE,
        "cleanup signature mismatch",
    )
    require(
        cleanup.get("finalized_slot") == PROGRAMDATA_CLOSE_SLOT, "cleanup slot mismatch"
    )
    require(
        cleanup.get("programdata_account_absent") is True,
        "cleanup did not report ProgramData closed",
    )
    refund = cleanup.get("refund", {})
    require(
        refund.get("refund_lamports") == PROGRAMDATA_REFUND_LAMPORTS,
        "cleanup refund mismatch",
    )
    require(
        refund.get("exact_refund_equation_reconciled") is True,
        "cleanup refund equation not reconciled",
    )

    projection = {
        "program_id": PROGRAM_ID,
        "sbf_sha256": SBF_SHA256,
        "proof_sha256": PROOF_SHA256,
        "verification_signature": VERIFICATION_SIGNATURE,
        "verification_slot": VERIFICATION_SLOT,
        "preclose_programdata_data_sha256": pd.get("data_sha256"),
        "programdata_close_signature": PROGRAMDATA_CLOSE_SIGNATURE,
        "programdata_refund_lamports": refund.get("refund_lamports"),
    }
    return {
        "selected_fact_sources": [
            "release/aspis-spend-q18-g37-mainnet-v1/evidence/mainnet-execution.json",
            "release/aspis-spend-q18-g37-mainnet-v1/evidence/mainnet-cleanup.json",
        ],
        "selected_facts_sha256": canonical_json_sha256(projection),
        "programdata_account_closed": True,
        "preclose_programdata_data_sha256": pd.get("data_sha256"),
        "programdata_refund_lamports": refund.get("refund_lamports"),
        "programdata_refund_equation_reconciled": True,
    }


def reconcile_record(
    official: RpcClient,
    independent: RpcClient,
    label: str,
    signature: str,
    expected_slot: int,
    expected_block_time: int,
    envelope_signature_count: int,
) -> dict[str, Any]:
    official_tx = raw_transaction(official, signature)
    independent_tx = raw_transaction(independent, signature)
    require(
        normalized_json_sha256(official_tx) == normalized_json_sha256(independent_tx),
        f"providers disagree on the raw {label} transaction",
    )
    tx = official_tx
    require(tx.get("slot") == expected_slot, f"{label} slot mismatch")
    require(tx.get("blockTime") == expected_block_time, f"{label} block time mismatch")
    meta = transaction_meta(tx)
    require(meta.get("err") is None, f"{label} transaction failed")
    validate_envelope_signatures(tx, signature, envelope_signature_count)
    message = transaction_message(tx)
    keys = account_keys(message)
    log_messages = meta.get("logMessages")
    require(isinstance(log_messages, list), f"{label} log messages are absent")

    official_status = signature_status(official, signature)
    independent_status = signature_status(independent, signature)
    require(official_status == independent_status, f"providers disagree on {label} status")
    require(official_status["present"] is True, f"{label} status absent")
    require(
        official_status["confirmation_status"] == "finalized",
        f"{label} not finalized",
    )

    return {
        "label": label,
        "signature": signature,
        "slot": tx.get("slot"),
        "block_time_unix": tx.get("blockTime"),
        "meta_err": meta.get("err"),
        "fee_lamports": meta.get("fee"),
        "compute_units_consumed": meta.get("computeUnitsConsumed"),
        "transaction_version": tx.get("version"),
        "account_key_count": len(keys),
        "account_keys": keys,
        "pre_balances": meta.get("preBalances"),
        "post_balances": meta.get("postBalances"),
        "log_message_count": len(log_messages),
        "log_messages_sha256": canonical_json_sha256(log_messages),
        "confirmation_status": official_status["confirmation_status"],
        "provider_normalized_raw_transaction_and_status_exactly_equal": True,
        "normalized_raw_transaction_sha256": normalized_json_sha256(tx),
    }


def account_absent(client: RpcClient, address: str) -> bool:
    result = client.call(
        "getAccountInfo", [address, {"encoding": "base64", "commitment": "finalized"}]
    )
    require(isinstance(result, dict), "getAccountInfo response is malformed")
    return result.get("value") is None


def build_reconciliation(
    official: RpcClient, independent: RpcClient
) -> dict[str, Any]:
    for client in (official, independent):
        require(
            client.call("getGenesisHash", []) == GENESIS_HASH,
            f"{client.label} genesis mismatch",
        )

    deploy = reconcile_record(
        official, independent, "deployment", DEPLOYMENT_SIGNATURE,
        DEPLOYMENT_SLOT, DEPLOYMENT_BLOCK_TIME, 3,
    )
    verify = reconcile_record(
        official, independent, "verification", VERIFICATION_SIGNATURE,
        VERIFICATION_SLOT, VERIFICATION_BLOCK_TIME, 2,
    )
    close = reconcile_record(
        official, independent, "programdata_close", PROGRAMDATA_CLOSE_SIGNATURE,
        PROGRAMDATA_CLOSE_SLOT, PROGRAMDATA_CLOSE_BLOCK_TIME, 2,
    )

    # Post-close account images: both providers must agree the ProgramData
    # account is now absent, while the Program account remains.
    official_pd_absent = account_absent(official, PROGRAMDATA_ADDRESS)
    independent_pd_absent = account_absent(independent, PROGRAMDATA_ADDRESS)
    require(
        official_pd_absent is True and independent_pd_absent is True,
        "providers disagree that the ProgramData account is closed",
    )
    official_prog_absent = account_absent(official, PROGRAM_ID)
    independent_prog_absent = account_absent(independent, PROGRAM_ID)
    require(
        official_prog_absent is False and independent_prog_absent is False,
        "providers disagree that the Program account remains",
    )

    # Cluster disambiguation: the verification signature is absent on devnet and
    # testnet, whose genesis hashes differ from mainnet.
    devnet = RpcClient("devnet RPC", DEVNET_RPC, official.timeout, official.retries, 0.0)
    testnet = RpcClient(
        "testnet RPC", TESTNET_RPC, official.timeout, official.retries, 0.0
    )
    require(devnet.call("getGenesisHash", []) == DEVNET_GENESIS, "devnet genesis drift")
    require(
        testnet.call("getGenesisHash", []) == TESTNET_GENESIS, "testnet genesis drift"
    )
    devnet_status = signature_status(devnet, VERIFICATION_SIGNATURE)
    testnet_status = signature_status(testnet, VERIFICATION_SIGNATURE)
    require(
        devnet_status["present"] is False and testnet_status["present"] is False,
        "verification signature unexpectedly present on devnet/testnet",
    )

    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": RECONCILIATION_ARTIFACT,
        "network": NETWORK,
        "genesis_hash": GENESIS_HASH,
        "deterministic": True,
        "reproduction": {
            "mode": "live_archival_json_rpc",
            "full_rpc_responses_serialized": False,
            "credential_material_serialized": False,
            "endpoint_hostname_or_origin_serialized": False,
            "fixed_provider_labels_serialized": True,
        },
        "rpc": {
            "provider_labels": ["official_rpc", "independent_rpc"],
            "commitment": "finalized",
            "transaction_encoding": "json",
            "max_supported_transaction_version": 0,
            "both_providers_report_mainnet_genesis": True,
        },
        "records": {
            "deployment": deploy,
            "verification": verify,
            "programdata_close": close,
        },
        "post_close_account_state": {
            "programdata_address": PROGRAMDATA_ADDRESS,
            "programdata_account_absent_on_both_providers": True,
            "program_address": PROGRAM_ID,
            "program_account_present_on_both_providers": True,
        },
        "cluster_disambiguation": {
            "verification_signature": VERIFICATION_SIGNATURE,
            "mainnet_genesis_hash": GENESIS_HASH,
            "devnet_genesis_hash": DEVNET_GENESIS,
            "testnet_genesis_hash": TESTNET_GENESIS,
            "verification_signature_present_on_devnet": False,
            "verification_signature_present_on_testnet": False,
        },
    }


def compare_substantive(actual: dict[str, Any], expected_path: pathlib.Path) -> None:
    expected = load_json(expected_path)
    actual_copy = dict(actual)
    expected_copy = dict(expected)
    actual_copy.pop("captured_at_utc", None)
    expected_copy.pop("captured_at_utc", None)
    require(
        actual_copy == expected_copy,
        "fresh result differs from the checked-in substantive fields",
    )


def build_result(args: argparse.Namespace) -> tuple[dict[str, Any], dict[str, Any] | None]:
    repo_root = pathlib.Path(__file__).resolve().parents[1]
    sbf_path = pathlib.Path(args.sbf_path).resolve()
    proof_path = pathlib.Path(args.proof_path).resolve()
    statement_path = pathlib.Path(args.statement_path).resolve()

    official = RpcClient(
        "official RPC", args.official_rpc, args.rpc_timeout, args.rpc_retries,
        args.official_rps,
    )
    independent = RpcClient(
        "independent RPC", args.independent_rpc, args.rpc_timeout, args.rpc_retries,
        args.independent_rps,
    )
    require(
        official.origin != independent.origin,
        "official and independent RPC origins must differ",
    )

    captured_at = dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")
    for client in (official, independent):
        require(
            client.call("getGenesisHash", []) == GENESIS_HASH,
            f"{client.label} genesis mismatch",
        )

    official_deploy_record, official_deploy_tx = verified_deployment_record(official)
    independent_deploy_record, independent_deploy_tx = verified_deployment_record(
        independent
    )
    require(
        official_deploy_record == independent_deploy_record
        and official_deploy_tx == independent_deploy_tx,
        "providers disagree on the deployment transaction or status",
    )

    official_predeployment, official_page_sizes = fetch_predeployment_history(official)
    independent_predeployment, independent_page_sizes = fetch_predeployment_history(
        independent
    )
    require(
        official_predeployment == independent_predeployment,
        "providers disagree on complete predeployment signature records",
    )
    require(
        official_page_sizes == independent_page_sizes == PAGE_SIZES_BEFORE_DEPLOYMENT,
        "before=deployment pagination shape mismatch",
    )
    history = [official_deploy_record, *official_predeployment]
    signatures = [record["signature"] for record in history]
    require(len(history) == HISTORY_COUNT, "selected buffer history count mismatch")
    require(
        all(record.get("err") is None for record in history),
        "selected history contains a failed transaction",
    )
    require(
        all(record.get("confirmationStatus") == "finalized" for record in history),
        "selected history contains a non-finalized transaction",
    )
    require(
        signatures[0] == DEPLOYMENT_SIGNATURE,
        "selected history does not start at deployment",
    )
    require(
        signatures[-1] == BUFFER_INITIALIZE_SIGNATURE,
        "selected history does not end at initialization",
    )
    canonical_history_hash = canonical_json_sha256(signatures)
    newline_history_hash = sha256_bytes("\n".join(signatures).encode("ascii"))

    validate_deployment(official, independent)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as provider_executor:
        official_future = provider_executor.submit(
            fetch_history_transactions, history, official, args.workers
        )
        independent_future = provider_executor.submit(
            fetch_history_transactions, history, independent, args.workers
        )
        official_transactions = official_future.result()
        independent_transactions = independent_future.result()
    require(
        official_transactions == independent_transactions,
        "providers disagree on normalized raw transaction results",
    )
    raw_transactions_sha256 = normalized_json_sha256(official_transactions)
    official_sbf, official_sbf_metrics = reconstruct_sbf(history, official_transactions)
    independent_sbf, independent_sbf_metrics = reconstruct_sbf(
        history, independent_transactions
    )
    require(
        official_sbf == independent_sbf
        and official_sbf_metrics == independent_sbf_metrics,
        "provider SBF reconstructions or metrics differ",
    )
    reconstructed_sbf = official_sbf
    sbf_metrics = official_sbf_metrics

    local_sbf = sbf_path.read_bytes()
    require(len(local_sbf) == SBF_BYTES, "bundle SBF length mismatch")
    require(sha256_bytes(local_sbf) == SBF_SHA256, "bundle SBF hash mismatch")
    require(local_sbf == reconstructed_sbf, "chain-reconstructed SBF differs from bundle")

    authority_bytes = base58_decode(UPGRADE_AUTHORITY)
    require(len(authority_bytes) == 32, "upgrade authority did not decode to 32 bytes")
    programdata_header = struct.pack("<IQB", 3, DEPLOYMENT_SLOT, 1) + authority_bytes
    require(len(programdata_header) == 45, "ProgramData header length mismatch")
    require(programdata_header.hex() == PROGRAMDATA_HEADER_HEX, "ProgramData header mismatch")
    programdata_image = programdata_header + reconstructed_sbf
    require(len(programdata_image) == PROGRAMDATA_BYTES, "ProgramData image length mismatch")
    require(
        sha256_bytes(programdata_image) == PROGRAMDATA_SHA256,
        "ProgramData image hash mismatch",
    )

    official_tag_transaction = raw_transaction(official, VERIFICATION_SIGNATURE)
    independent_tag_transaction = raw_transaction(independent, VERIFICATION_SIGNATURE)
    require(
        official_tag_transaction == independent_tag_transaction,
        "providers disagree on the raw tag65 transaction result",
    )
    official_tag = parse_tag65(official_tag_transaction)
    independent_tag = parse_tag65(independent_tag_transaction)
    require(official_tag == independent_tag, "providers disagree on the tag65 transaction")
    official_status = signature_status(official, VERIFICATION_SIGNATURE)
    independent_status = signature_status(independent, VERIFICATION_SIGNATURE)
    require(official_status == independent_status, "providers disagree on verification status")
    require(official_status["slot"] == VERIFICATION_SLOT, "verification status slot mismatch")
    require(
        official_status["confirmation_status"] == "finalized",
        "verification is not finalized",
    )
    require(official_status["err"] is None, "verification status records an error")
    official_tag["confirmation_status"] = "finalized"
    official_tag["provider_raw_transaction_and_status_exactly_equal"] = True

    local_proof = proof_path.read_bytes()
    require(len(local_proof) == PROOF_BYTES, "bundle proof length mismatch")
    require(sha256_bytes(local_proof) == PROOF_SHA256, "bundle proof hash mismatch")
    statement = load_json(statement_path)
    for key, value in official_tag["decoded"].items():
        if key == "tag":
            continue
        statement_key = {"asset_id_u32_le": "asset_id", "fee_u32_le": "fee"}.get(key, key)
        require(
            statement.get(statement_key) == value,
            f"statement field mismatch: {statement_key}",
        )

    evidence_cross_checks = validate_checked_in_evidence(repo_root)

    history_object = {
        "address": BUFFER_ADDRESS,
        "selection": (
            "separately verified deployment record prepended to "
            "getSignaturesForAddress(before=deployment) records through buffer "
            "initialization; later address reuse cannot affect the selected slice"
        ),
        "ordering": (
            "deployment followed by predeployment records newest-to-oldest "
            "through initialization"
        ),
        "backward_rpc_page_sizes": official_page_sizes,
        "page_1_last_signature": signatures[999],
        "count": len(signatures),
        "failed_count": 0,
        "non_finalized_count": 0,
        "newest_signature": signatures[0],
        "oldest_signature": signatures[-1],
        "newest_slot": history[0]["slot"],
        "oldest_slot": history[-1]["slot"],
        "newest_block_time_unix": history[0]["blockTime"],
        "oldest_block_time_unix": history[-1]["blockTime"],
        "canonicalization": (
            "UTF-8 compact JSON array of selected signature strings, "
            "newest-to-oldest, no spaces or trailing newline"
        ),
        "canonical_json_sha256": canonical_history_hash,
        "newline_joined_no_trailing_newline_sha256": newline_history_hash,
        "provider_complete_signature_records_exactly_equal": True,
        "deployment_transaction_and_status_separately_verified": True,
    }

    result = {
        "schema_version": SCHEMA_VERSION,
        "artifact": ARTIFACT,
        "captured_at_utc": captured_at,
        "network": NETWORK,
        "genesis_hash": GENESIS_HASH,
        "reproduction": {
            "mode": "live_archival_json_rpc",
            "live_rpc_or_equivalent_local_cache_required": True,
            "full_rpc_responses_serialized": False,
            "credential_material_serialized": False,
            "endpoint_hostname_or_origin_serialized": False,
            "fixed_provider_labels_serialized": True,
            "deterministic_except": ["captured_at_utc"],
        },
        "rpc": {
            "provider_labels": ["official_rpc", "independent_rpc"],
            "commitment": "finalized",
            "transaction_encoding": "json",
            "max_supported_transaction_version": 0,
            "buffer_signature_history": history_object,
        },
        "deployment": {
            "signature": DEPLOYMENT_SIGNATURE,
            "slot": DEPLOYMENT_SLOT,
            "block_time_unix": DEPLOYMENT_BLOCK_TIME,
            "meta_err": None,
            "loader_program": LOADER_ID,
            "program_id": PROGRAM_ID,
            "programdata_address": PROGRAMDATA_ADDRESS,
            "buffer_address": BUFFER_ADDRESS,
            "upgrade_authority": UPGRADE_AUTHORITY,
            "payer": PAYER,
            "max_data_len": SBF_BYTES,
            "buffer_create_initialize_signature": BUFFER_INITIALIZE_SIGNATURE,
            "buffer_space": BUFFER_SPACE,
            "buffer_lamports": BUFFER_LAMPORTS,
            "provider_raw_transaction_and_status_exactly_equal": True,
        },
        "sbf_reconstruction": {
            "transaction_body_provider_labels": ["official_rpc", "independent_rpc"],
            "provider_normalized_raw_transaction_results_exactly_equal": True,
            "normalized_raw_transaction_results_sha256": raw_transactions_sha256,
            "provider_byte_images_and_metrics_exactly_equal": True,
            **sbf_metrics,
            "bundle_sbf_bytes": len(local_sbf),
            "bundle_sbf_sha256": sha256_bytes(local_sbf),
            "byte_for_byte_equal_to_bundle": True,
        },
        "programdata_reconstruction": {
            "programdata_account_closed": True,
            "loader_v3_header_bytes": len(programdata_header),
            "header_hex": programdata_header.hex(),
            "encoding": (
                "u32_le ProgramData discriminator 3 || u64_le deployment slot "
                f"{DEPLOYMENT_SLOT} || Some tag 1 || 32-byte upgrade-authority pubkey"
            ),
            "header_plus_sbf_bytes": len(programdata_image),
            "header_plus_sbf_sha256": sha256_bytes(programdata_image),
            "recorded_preclose_programdata_sha256": PROGRAMDATA_SHA256,
            "recorded_preclose_programdata_source": (
                "release/aspis-spend-q18-g37-mainnet-v1/evidence/"
                "mainnet-execution.json"
            ),
            "exact": True,
        },
        "proof": {
            "bundle_bytes": len(local_proof),
            "bundle_sha256": sha256_bytes(local_proof),
            "finalized_program_log_sha256": official_tag["proof_log"]["proof_sha256"],
            "log_matches_bundle": True,
        },
        "tag65_instruction": official_tag,
        "checked_in_evidence_cross_checks": evidence_cross_checks,
    }

    reconciliation = None
    if args.reconciliation_output:
        reconciliation = build_reconciliation(official, independent)

    return result, reconciliation


def parse_args(argv: list[str]) -> argparse.Namespace:
    repo_root = pathlib.Path(__file__).resolve().parents[1]
    bundle = repo_root / "release/aspis-spend-q18-g37-mainnet-v1"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", required=True, help="reconstruction JSON path, or '-' for stdout"
    )
    parser.add_argument(
        "--reconciliation-output",
        dest="reconciliation_output",
        help="optional deterministic two-RPC reconciliation JSON path",
    )
    parser.add_argument("--official-rpc", default=OFFICIAL_RPC, help="official/main RPC URL")
    parser.add_argument(
        "--independent-rpc", default=INDEPENDENT_RPC, help="independent RPC URL"
    )
    parser.add_argument(
        "--sbf-path", default=str(bundle / "program/aspis_verifier.so")
    )
    parser.add_argument(
        "--proof-path", default=str(bundle / "proof/spend-q18-g37.bin")
    )
    parser.add_argument(
        "--statement-path", default=str(bundle / "proof/statement.json")
    )
    parser.add_argument("--workers", type=int, default=8, help="parallel tx fetches")
    parser.add_argument(
        "--official-rps", type=float, default=0.9,
        help="shared official-RPC request rate; 0 disables pacing",
    )
    parser.add_argument(
        "--independent-rps", type=float, default=0.0,
        help="shared independent-RPC request rate; 0 disables pacing",
    )
    parser.add_argument("--rpc-timeout", type=float, default=60.0)
    parser.add_argument("--rpc-retries", type=int, default=20)
    parser.add_argument(
        "--compare-substantive",
        help="checked-in reconstruction JSON to compare while ignoring captured_at_utc",
    )
    args = parser.parse_args(argv)
    require(1 <= args.workers <= 32, "workers must be between 1 and 32")
    require(args.official_rps >= 0, "official RPS must be nonnegative")
    require(args.independent_rps >= 0, "independent RPS must be nonnegative")
    require(args.rpc_timeout > 0, "RPC timeout must be positive")
    require(args.rpc_retries >= 1, "RPC retries must be positive")
    return args


def write_output(path_arg: str, value: dict[str, Any]) -> None:
    encoded = json.dumps(value, ensure_ascii=False, indent=2) + "\n"
    if path_arg == "-":
        sys.stdout.write(encoded)
    else:
        output_path = pathlib.Path(path_arg)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(encoded, encoding="utf-8")
        print(f"wrote {output_path}")


def main(argv: list[str]) -> int:
    try:
        args = parse_args(argv)
        result, reconciliation = build_result(args)
        if args.compare_substantive:
            compare_substantive(result, pathlib.Path(args.compare_substantive))
        write_output(args.output, result)
        if reconciliation is not None:
            write_output(args.reconciliation_output, reconciliation)
        return 0
    except ReconstructionError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    except OSError as error:
        print(
            "ERROR: local file operation failed: "
            f"{error.strerror or error.__class__.__name__}",
            file=sys.stderr,
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
