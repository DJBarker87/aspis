#!/usr/bin/env python3
"""Check the canonical Aspis release facts against artifacts and public claims."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LEDGER_PATH = ROOT / "release/release-facts.json"
PUBLIC_SUFFIXES = {".cff", ".md", ".html", ".tex", ".rst", ".txt"}
IMMUTABLE_RELEASE_PREFIXES = (
    "release/aspis-spend-q18-g37-mainnet-v1/",
    "release/aspis-v5-tag67-frozen-candidate-v1/",
)

KNOWN_STALE_PATTERNS = (
    (
        "superseded V5 accepted-state ceiling",
        re.compile(r"(?<![\d,])(?:1,356,762|1356762)(?!\d)"),
    ),
    (
        "superseded V5 accepted-state headroom",
        re.compile(r"(?<![\d,])(?:43,238|43238)(?!\d)"),
    ),
    (
        "unscoped accepted-state CU claim",
        re.compile(
            r"\baccepted[- ]state (?:CU |compute )?(?:ceiling|bound|envelope)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "unscoped accepted-input CU claim",
        re.compile(
            r"\baccepted[- ]input (?:CU |compute )?(?:ceiling|bound|envelope)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "obsolete universal CU policy label",
        re.compile(r"\buniversal CU policy\b", re.IGNORECASE),
    ),
    (
        "obsolete feature-gated V5 status",
        re.compile(r"\bcurrent feature[- ]gated candidate[- ]v5 code\b", re.IGNORECASE),
    ),
    (
        "obsolete local-feature candidate status",
        re.compile(r"\bfrozen local feature candidate\b", re.IGNORECASE),
    ),
    (
        "obsolete default-feature status",
        re.compile(
            r"\b(?:not enabled by default|disabled by default|"
            r"v5-production-tag67 (?:is|remains) non[- ]default)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "obsolete unapplied-switch status",
        re.compile(r"\b(?:prepared )?switch remains unapplied\b", re.IGNORECASE),
    ),
    (
        "obsolete release gate status",
        re.compile(
            r"\b(?:production-default|mainnet)[^\n]{0,48}\bNO[- ]GO\b|"
            r"\bwaiting only on Stream\b|\bremaining gate:\s*Stream\b",
            re.IGNORECASE,
        ),
    ),
    (
        "stale worktree process note",
        re.compile(r"\bNo file was staged, committed, or pushed\b", re.IGNORECASE),
    ),
    (
        "false positive V5 mainnet execution status",
        re.compile(
            r"\bV5\b[^\n.]{0,80}\b(?:has|was|is)\s+(?:already\s+)?"
            r"(?:been\s+)?(?:deployed|executed|finalized|landed)\s+"
            r"(?:on|to)\s+mainnet\b",
            re.IGNORECASE,
        ),
    ),
)


class DuplicateKeyError(ValueError):
    pass


def no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=no_duplicate_keys)
    except (OSError, UnicodeError, json.JSONDecodeError, DuplicateKeyError) as error:
        raise AssertionError(f"{path.relative_to(ROOT)}: invalid JSON: {error}") from error
    if not isinstance(value, dict):
        raise AssertionError(f"{path.relative_to(ROOT)}: top-level JSON value is not an object")
    return value


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def require_equal(actual: Any, expected: Any, label: str) -> None:
    require(actual == expected, f"{label}: expected {expected!r}, found {actual!r}")


def require_file_identity(path_value: str, expected_bytes: int, expected_sha256: str) -> None:
    path = ROOT / path_value
    require(path.is_file(), f"{path_value}: file is missing")
    require_equal(path.stat().st_size, expected_bytes, f"{path_value} byte length")
    require_equal(sha256(path), expected_sha256, f"{path_value} SHA-256")


def git_output(*arguments: str) -> str:
    result = subprocess.run(
        ["git", *arguments],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise AssertionError(f"git {' '.join(arguments)} failed: {detail}")
    return result.stdout.decode("utf-8").strip()


def tag_commit(tag: str) -> str:
    return git_output("rev-parse", f"{tag}^{{commit}}")


def object_tree(object_name: str) -> str:
    return git_output("rev-parse", f"{object_name}^{{tree}}")


def check_q18(facts: dict[str, Any], compute_limit: int) -> None:
    require_equal(facts["role"], "finalized_mainnet_release", "q18 role")
    require_equal(facts["status"], "finalized_mainnet", "q18 status")
    require(facts["build_source_commit"] is None, "q18 build_source_commit must remain null")
    require_equal(
        facts["build_source_commit_status"],
        "not_recorded_in_immutable_release_bundle",
        "q18 build-source status",
    )
    require_equal(
        tag_commit(facts["release_tag"]),
        facts["release_tag_commit"],
        "q18 release tag commit",
    )
    require_equal(
        object_tree(facts["release_tag"]),
        facts["release_tag_tree"],
        "q18 release tag tree",
    )

    sources = facts["authoritative_sources"]
    manifest = load_json(ROOT / sources["manifest"])
    certificate = load_json(ROOT / sources["release_certificate"])
    execution = load_json(ROOT / sources["execution"])
    program = facts["program"]
    proof = facts["proof"]
    transaction = facts["mainnet"]["transaction"]

    require_equal(manifest["release_id"], facts["release_tag"], "q18 manifest release id")
    require_equal(manifest["network"], facts["runtime"]["network"], "q18 network")
    require_equal(
        manifest["mainnet_genesis_hash"],
        facts["runtime"]["genesis_hash"],
        "q18 genesis hash",
    )
    require(facts["runtime"]["solana_core"] is None, "q18 solana_core must remain null")
    require(facts["runtime"]["feature_set"] is None, "q18 feature_set must remain null")
    require_equal(manifest["program_id"], program["id"], "q18 program id")
    require_equal(manifest["sbf_sha256"], program["sbf_sha256"], "q18 manifest SBF hash")
    require_equal(manifest["proof_sha256"], proof["sha256"], "q18 manifest proof hash")
    require_equal(
        manifest["objects"]["program/aspis_verifier.so"]["bytes"],
        program["sbf_bytes"],
        "q18 manifest SBF bytes",
    )
    require_equal(
        manifest["objects"]["proof/spend-q18-g37.bin"]["bytes"],
        proof["bytes"],
        "q18 manifest proof bytes",
    )
    require_file_identity(program["sbf_path"], program["sbf_bytes"], program["sbf_sha256"])
    require_file_identity(proof["path"], proof["bytes"], proof["sha256"])

    manifest_transaction = manifest["finalized_transaction"]
    require_equal(manifest_transaction["signature"], transaction["signature"], "q18 signature")
    require_equal(manifest_transaction["finalized_slot"], transaction["slot"], "q18 slot")
    require_equal(
        manifest_transaction["compute_units_consumed"],
        transaction["compute_units"],
        "q18 measured CU",
    )
    require_equal(
        execution["final_transaction"]["signature"],
        transaction["signature"],
        "q18 execution signature",
    )
    require_equal(
        execution["final_transaction"]["compute_units_consumed"],
        facts["compute"]["measured_transaction_cu"],
        "q18 execution CU",
    )
    require_equal(
        transaction["compute_units"],
        facts["compute"]["measured_transaction_cu"],
        "q18 ledger CU",
    )
    require_equal(certificate["compute_unit_limit"], compute_limit, "q18 CU limit")
    require_equal(
        certificate["max_literal_production_tag65_cu"],
        facts["compute"]["release_gate_max_literal_cu"],
        "q18 release-gate CU",
    )
    require_equal(
        certificate["exact_headroom_under_1_4m_cu"],
        facts["compute"]["release_gate_headroom_cu"],
        "q18 release-gate headroom",
    )
    require_equal(
        facts["compute"]["release_gate_max_literal_cu"]
        + facts["compute"]["release_gate_headroom_cu"],
        compute_limit,
        "q18 release-gate CU arithmetic",
    )


def measurement_totals(runtime: dict[str, Any], marker_mode: str) -> dict[str, int]:
    result: dict[str, int] = {}
    for measurement in runtime["measurements"]:
        if measurement["marker_mode"] != marker_mode:
            continue
        totals = measurement["totals_cu"]
        require(
            len(totals) == 3 and len(set(totals)) == 1,
            f"V5 selector {measurement['selector']} totals are not three identical measurements",
        )
        result[str(measurement["selector"])] = totals[0]
    return result


def check_v5(facts: dict[str, Any], compute_limit: int) -> None:
    require_equal(facts["role"], "mainnet_candidate", "V5 role")
    require_equal(facts["status"], "ready_for_mainnet_deployment", "V5 status")
    require(facts["mainnet"]["transaction"] is None, "V5 mainnet transaction must remain null")
    require(
        facts["mainnet"]["deployment_transaction"] is None,
        "V5 mainnet deployment transaction must remain null",
    )
    require_equal(facts["mainnet"]["deployment_status"], "not_deployed", "V5 deployment status")
    require_equal(
        tag_commit(facts["candidate_tag"]),
        facts["candidate_tag_commit"],
        "V5 candidate tag commit",
    )
    require_equal(
        object_tree(facts["candidate_tag"]),
        facts["candidate_tag_tree"],
        "V5 candidate tag tree",
    )
    require_equal(
        git_output("rev-parse", f"{facts['build_source_commit']}^{{commit}}"),
        facts["build_source_commit"],
        "V5 build source commit",
    )
    require_equal(
        object_tree(facts["build_source_commit"]),
        facts["build_source_tree"],
        "V5 build source tree",
    )

    sources = facts["authoritative_sources"]
    manifest = load_json(ROOT / sources["manifest"])
    devnet_execution = load_json(ROOT / sources["devnet_execution"])
    frozen_policy = load_json(ROOT / sources["frozen_compute_policy"])
    runtime_path = ROOT / sources["current_runtime_replay"]
    runtime = load_json(runtime_path)
    program = facts["program"]
    devnet = facts["devnet"]
    current = facts["runtime"]["current_mainnet_replay"]
    frozen = facts["runtime"]["frozen_cost_schedule"]

    require_equal(manifest["release_id"], facts["candidate_tag"], "V5 manifest release id")
    require_equal(manifest["source"]["commit"], facts["build_source_commit"], "V5 build source")
    require_equal(manifest["source"]["tree"], facts["build_source_tree"], "V5 build source tree")
    require_equal(
        manifest["source"]["clean_rebuild_byte_equal"],
        facts["clean_rebuild_byte_equal"],
        "V5 clean rebuild result",
    )
    require_equal(
        manifest["candidate"]["declared_program_id"],
        program["declared_id"],
        "V5 declared program id",
    )
    require_equal(manifest["candidate"]["sbf_bytes"], program["sbf_bytes"], "V5 SBF bytes")
    require_equal(manifest["candidate"]["sbf_sha256"], program["sbf_sha256"], "V5 SBF hash")
    require_file_identity(program["sbf_path"], program["sbf_bytes"], program["sbf_sha256"])

    manifest_devnet = manifest["devnet"]
    require_equal(manifest_devnet["genesis_hash"], devnet["genesis_hash"], "V5 devnet genesis")
    require_equal(manifest_devnet["program_id"], devnet["program_id"], "V5 devnet program")
    require_equal(manifest_devnet["pool"], devnet["pool"], "V5 devnet pool")
    require_equal(
        manifest_devnet["proof_account"],
        devnet["proof_account"],
        "V5 devnet proof account",
    )
    require_equal(
        manifest_devnet["nullifier_address"],
        devnet["nullifier"],
        "V5 devnet nullifier",
    )
    require_equal(manifest_devnet["proof_sha256"], devnet["proof_sha256"], "V5 devnet proof hash")
    require_equal(
        manifest_devnet["statement_sha256"],
        devnet["statement_sha256"],
        "V5 devnet statement hash",
    )
    manifest_transaction = manifest_devnet["finalized_transaction"]
    require_equal(
        manifest_transaction["signature"],
        devnet["transaction"]["signature"],
        "V5 devnet signature",
    )
    require_equal(manifest_transaction["slot"], devnet["transaction"]["slot"], "V5 devnet slot")
    require_equal(
        manifest_transaction["compute_units"],
        facts["compute"]["devnet_measured_transaction_cu"],
        "V5 devnet CU",
    )
    require_equal(
        devnet_execution["final_transaction"]["signature"],
        devnet["transaction"]["signature"],
        "V5 devnet execution signature",
    )
    require_equal(
        devnet_execution["final_transaction"]["finalized_slot"],
        devnet["transaction"]["slot"],
        "V5 devnet execution slot",
    )
    require_equal(
        devnet_execution["final_transaction"]["compute_units_consumed"],
        devnet["transaction"]["compute_units"],
        "V5 devnet execution CU",
    )
    require_equal(
        devnet["transaction"]["compute_units"],
        facts["compute"]["devnet_measured_transaction_cu"],
        "V5 devnet ledger CU",
    )

    require_equal(
        frozen_policy["transaction_cu_limit"],
        compute_limit,
        "V5 frozen-policy CU limit",
    )
    require_equal(frozen["solana_core"], "2.3.13", "V5 frozen runtime")
    require_equal(
        frozen_policy["universal_accepted_input_upper_bound_cu"],
        frozen["bump_255_topology_ceiling_cu"],
        "V5 frozen bump-255 topology ceiling",
    )
    require_equal(
        frozen_policy["universal_headroom_cu"],
        frozen["bump_255_topology_headroom_cu"],
        "V5 frozen bump-255 topology headroom",
    )

    require_equal(sha256(runtime_path), current["evidence_sha256"], "V5 runtime replay hash")
    require_equal(runtime["source_base_commit"], current["source_base_commit"], "V5 replay base")
    require_equal(runtime["sbf"]["bytes"], program["sbf_bytes"], "V5 replay SBF bytes")
    require_equal(runtime["sbf"]["sha256"], program["sbf_sha256"], "V5 replay SBF hash")
    require_equal(
        runtime["mainnet_beta"]["observed_finalized_slot"],
        current["observed_finalized_slot"],
        "V5 replay observation slot",
    )
    require_equal(
        runtime["mainnet_beta"]["solana_core"],
        current["solana_core"],
        "V5 current runtime",
    )
    require_equal(
        runtime["mainnet_beta"]["feature_set"],
        current["feature_set"],
        "V5 current feature set",
    )
    require_equal(
        measurement_totals(runtime, "prefunded_system_owned_one_lamport"),
        facts["compute"]["current_mainnet_priced_prefunded_by_selector_cu"],
        "V5 current priced prefunded measurements",
    )
    policy = runtime["accepted_input_policy"]
    require_equal(
        policy["accepted_state_ceiling_cu"],
        facts["compute"]["current_mainnet_release_policy_ceiling_cu"],
        "V5 current release-policy ceiling",
    )
    require_equal(
        policy["accepted_state_headroom_cu"],
        facts["compute"]["current_mainnet_release_policy_headroom_cu"],
        "V5 current release-policy headroom",
    )
    require_equal(
        facts["compute"]["current_mainnet_release_policy_ceiling_cu"]
        + facts["compute"]["current_mainnet_release_policy_headroom_cu"],
        compute_limit,
        "V5 current CU arithmetic",
    )
    require_equal(
        facts["compute"]["ceiling_scope"],
        "mainnet_runner_exact_signed_wire_simulation_with_canonical_nullifier_pda_bump_255",
        "V5 current CU scope",
    )
    require_equal(
        facts["compute"]["required_nullifier_pda_bump"],
        255,
        "V5 required nullifier PDA bump",
    )
    require_equal(
        facts["compute"]["pda_derivation_attempts"],
        256 - facts["compute"]["required_nullifier_pda_bump"],
        "V5 nullifier PDA derivation attempts",
    )
    require_equal(
        facts["compute"]["exact_signed_wire_simulation_required"],
        True,
        "V5 exact signed-wire simulation gate",
    )
    require_equal(
        facts["compute"]["exact_signed_wire_simulation_max_cu"],
        facts["compute"]["current_mainnet_release_policy_ceiling_cu"],
        "V5 exact signed-wire simulation ceiling",
    )
    require_equal(
        facts["compute"]["transaction_compute_unit_limit_cu"],
        facts["compute"]["current_mainnet_release_policy_ceiling_cu"],
        "V5 transaction compute-unit limit",
    )
    require_literals(
        "xtask/src/spend_devnet/v5.rs",
        [
            "const MAINNET_NULLIFIER_PDA_BUMP: u8 = u8::MAX;",
            "const MAINNET_RELEASE_POLICY_CU_CEILING: u64 = 1_356_912;",
            "ComputeBudgetInstruction::set_compute_unit_limit(tag67_compute_unit_limit)",
            "final_transaction_simulation_cu <= u64::from(tag67_compute_unit_limit)",
        ],
    )


def tracked_public_paths() -> list[Path]:
    raw = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if raw.returncode != 0:
        detail = raw.stderr.decode("utf-8", errors="replace").strip()
        raise AssertionError(f"git ls-files failed: {detail}")
    paths: list[Path] = []
    for entry in raw.stdout.split(b"\0"):
        if not entry:
            continue
        relative = entry.decode("utf-8")
        if relative.startswith(IMMUTABLE_RELEASE_PREFIXES):
            continue
        path = Path(relative)
        if path.suffix.lower() in PUBLIC_SUFFIXES:
            paths.append(path)
    return paths


def stale_claims(path: Path, text: str) -> list[str]:
    findings: list[str] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        for label, pattern in KNOWN_STALE_PATTERNS:
            if pattern.search(line):
                findings.append(f"{path}:{line_number}: {label}: {line.strip()}")
    return findings


def require_literals(path_value: str, values: list[str]) -> None:
    text = (ROOT / path_value).read_text(encoding="utf-8")
    for value in values:
        require(value in text, f"{path_value}: missing release fact {value!r}")


def check_public_claims(facts: dict[str, Any]) -> None:
    findings: list[str] = []
    for path in tracked_public_paths():
        try:
            text = (ROOT / path).read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise AssertionError(f"{path}: cannot read tracked public file: {error}") from error
        findings.extend(stale_claims(path, text))
    require(not findings, "tracked public release claims disagree:\n" + "\n".join(findings))

    q18 = facts["tracks"]["q18_g37_tag65_mainnet_v1"]
    v5 = facts["tracks"]["v5_tag67_candidate_v1"]
    require_literals(
        "README.md",
        [
            q18["mainnet"]["transaction"]["signature"],
            f"{q18['compute']['measured_transaction_cu']:,}",
            v5["devnet"]["transaction"]["signature"],
            f"{v5['compute']['devnet_measured_transaction_cu']:,}",
            f"{v5['compute']['current_mainnet_release_policy_ceiling_cu']:,}",
            f"{v5['compute']['current_mainnet_release_policy_headroom_cu']:,}",
            v5["program"]["sbf_sha256"],
            "exact signed-wire simulation",
            "canonical nullifier PDA bump",
            "transaction compute limit",
            "ready for mainnet deployment",
        ],
    )
    require_literals(
        "CITATION.cff",
        [
            q18["release_tag"],
            q18["release_tag_commit"],
        ],
    )
    require_literals(
        "docs/mainnet-demo.md",
        [
            q18["mainnet"]["transaction"]["signature"],
            str(q18["mainnet"]["transaction"]["slot"]),
            f"{q18['compute']['measured_transaction_cu']:,}",
            q18["program"]["id"],
        ],
    )
    require_literals(
        "release/preflight/v5-production-freeze.md",
        [
            "V5 has not yet been deployed on mainnet.",
            v5["program"]["sbf_sha256"],
            f"{v5['compute']['current_mainnet_release_policy_ceiling_cu']:,}",
            f"{v5['compute']['current_mainnet_release_policy_headroom_cu']:,}",
            "PDA bump is 255",
            "exact signed-wire simulation",
            "transaction compute limit",
        ],
    )
    require_literals(
        "paper/aspis-spend/sections/formalization.tex",
        ["V5 has not yet been executed on mainnet."],
    )
    require_literals(
        "results/spend/v5-mainnet-runtime-4.1.0-20260723/README.md",
        [
            f"{v5['compute']['current_mainnet_release_policy_ceiling_cu']:,}",
            f"{v5['compute']['current_mainnet_release_policy_headroom_cu']:,}",
            "exact signed-wire simulation",
        ],
    )


def self_test() -> None:
    path = Path("synthetic-public-claim.md")
    stale_examples = (
        "The current ceiling is 1,356,762 CU.",
        "Current headroom is 43,238 CU.",
        "The accepted-state ceiling is 1,353,616 CU.",
        "The accepted-state ceiling is 1,356,912 CU.",
        "The accepted-input CU bound is 1,356,912 CU.",
        "The universal CU policy passed.",
        "This is current feature-gated candidate-v5 code.",
        "The v5-production-tag67 feature is not enabled by default.",
        "The prepared switch remains unapplied.",
        "Production-default remains NO-GO.",
        "No file was staged, committed, or pushed.",
        "V5 has already been deployed on mainnet.",
    )
    for example in stale_examples:
        require(stale_claims(path, example), f"self-test did not reject {example!r}")
    clean = (
        "V5 has not yet been deployed on mainnet. "
        "It is ready for mainnet deployment. The runner requires an exact "
        "signed-wire simulation at or below 1,356,912 CU, leaving 43,088 CU "
        "of headroom. "
        "The immutable 2.3.13 bump-255 topology ceiling remains "
        "1,353,616 CU."
    )
    require(not stale_claims(path, clean), "self-test rejected the current release statement")
    print("PASS: release-facts stale-claim self-test")


def check() -> None:
    facts = load_json(LEDGER_PATH)
    require_equal(facts["artifact"], "aspis_release_facts", "ledger artifact")
    require_equal(facts["schema_version"], 2, "ledger schema version")
    require(
        re.fullmatch(r"\d{4}-\d{2}-\d{2}", facts["facts_as_of_date"]) is not None,
        "facts_as_of_date must use YYYY-MM-DD",
    )
    compute_limit = facts["transaction_compute_limit_cu"]
    require_equal(compute_limit, 1_400_000, "transaction CU limit")
    tracks = facts["tracks"]
    require_equal(
        set(tracks),
        {"q18_g37_tag65_mainnet_v1", "v5_tag67_candidate_v1"},
        "release track set",
    )
    check_q18(tracks["q18_g37_tag65_mainnet_v1"], compute_limit)
    check_v5(tracks["v5_tag67_candidate_v1"], compute_limit)
    check_public_claims(facts)
    print("PASS: release facts match artifacts, tags, runtime evidence, and public claims")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="exercise stale-claim rejection cases before checking the repository",
    )
    arguments = parser.parse_args()
    try:
        if arguments.self_test:
            self_test()
        check()
    except (AssertionError, KeyError, TypeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
