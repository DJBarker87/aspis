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
V5_FORMAL_EVIDENCE_PATH = (
    "release/aspis-v5-tag67-mainnet-v1/formal/formal-evidence.json"
)
V5_PRINCIPAL_INTEGRATION_THEOREM = (
    "FormalClosureStream1.current_source_combined_capstone"
)
V5_FORMAL_COVERAGE_STATUS = (
    "selected_component_correspondence_not_end_to_end_acceptance"
)
V5_TAG67_WORK_THEOREM_BOUNDARY = (
    "exact_transcript_hash_function_call_equality"
)
V5_TAG67_WORK_THEOREM_BOUNDARY_STATEMENT = (
    "forall state nonce, actualTranscriptGrindingDigest state nonce = "
    "rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))"
)
V5_POST_RELEASE_REVIEW_DATE = "2026-08-14"
V5_POST_RELEASE_REVIEW_COMMIT = "598fe3389ef492e10437e28c4c013507d405eb1a"
V5_POST_RELEASE_REVIEW_STATUS = "conditional_not_end_to_end"
V5_POST_RELEASE_REVIEW_PAGE = "docs/reviews/mathematical-status-20260814.md"
V5_POST_RELEASE_REVIEW_THEOREMS = {
    "normalized_trace_to_spend_relation": (
        "AspisV5AcceptedSpendRelation.extracted_trace_implies_spend_relation"
    ),
    "accepted_run_schema": (
        "AspisV5AcceptedSpendRelation."
        "accepted_run_implies_spend_relation_or_bad_event"
    ),
    "false_accept_event_bound": (
        "AspisV5AcceptedSpendRelation.false_accept_measure_le_bad_event"
    ),
    "wrong_secret_event_bound": (
        "AspisV5TheftResistance.wrong_secret_measure_le_bad_events"
    ),
    "same_leaf_different_opening_event_bound": (
        "AspisV5TheftResistance."
        "different_opening_same_leaf_measure_le_bad_events"
    ),
}
V5_POST_RELEASE_REMAINING_BOUNDARY_KINDS = (
    "accepted_tag67_to_normalized_trace_and_public_state",
    "pcs_fri_fiat_shamir_soundness_and_failure_bound",
    "deployed_poseidon2_faithfulness",
    "tag67_transcript_hash_call_equality",
    "deployed_knowledge_and_simulation_extraction",
    "fixed_target_commitment_security_and_numeric_bounds",
    "alternative_leaf_merkle_binding_and_complete_theft_game",
)
V5_POST_RELEASE_REPLAY_COMMAND = (
    "cd AspisFormal && lake build AspisFormal.V5AcceptedSpendRelation "
    "AspisFormal.TheftResistance AspisFormal.V5TheftResistance"
)
V5_FORMAL_COVERAGE = (
    "Component-A matrix execution at the selected V5 release schedule",
    "Component-B sampler, evaluator, and C2 layout correspondence",
    "Component-C four runtime rounds, finish, packer, and deployed public output",
    "Tag-67 instruction guards and six actual little-endian 64-bit work reads",
    "The digest predicate and all six ordered work-verification steps",
    "Composition of those results for the stated V5 release scope",
)
V5_FORMAL_REPLAY_COMMANDS = (
    "cd AspisFormal && lake exe cache get && lake build",
    (
        "aeneas-verif/component-c-runtime-downstream/"
        "released-trace-families-current-20260722/replay-lean432.sh"
    ),
    "aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh",
)
V5_REQUIRED_FORMAL_ARTIFACTS = {
    (
        "aeneas-verif/current-source-abc-capstone-20260722/proof/"
        "CurrentSourceABCapstone.lean"
    ),
    (
        "aeneas-verif/component-c-runtime-downstream/"
        "released-trace-families-current-20260722/proof/"
        "RuntimeReleasedTraceFamiliesCurrentJoin.lean"
    ),
    (
        "aeneas-verif/tag67-work-wire-correspondence/proof/"
        "Tag67WorkVerifierClosure.lean"
    ),
    (
        "aeneas-verif/component-c-runtime-downstream/"
        "released-trace-families-current-20260722/replay-lean432.sh"
    ),
    "aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh",
}
V5_REQUIRED_POST_RELEASE_REVIEW_ARTIFACTS = {
    "AspisFormal/AspisFormal/TheftResistance.lean",
    "AspisFormal/AspisFormal/V5AcceptedSpendRelation.lean",
    "AspisFormal/AspisFormal/V5TheftResistance.lean",
}
V5_POST_RELEASE_THEOREM_SOURCE_PATHS = {
    "normalized_trace_to_spend_relation": (
        "AspisFormal/AspisFormal/V5AcceptedSpendRelation.lean"
    ),
    "accepted_run_schema": "AspisFormal/AspisFormal/V5AcceptedSpendRelation.lean",
    "false_accept_event_bound": (
        "AspisFormal/AspisFormal/V5AcceptedSpendRelation.lean"
    ),
    "wrong_secret_event_bound": "AspisFormal/AspisFormal/V5TheftResistance.lean",
    "same_leaf_different_opening_event_bound": (
        "AspisFormal/AspisFormal/V5TheftResistance.lean"
    ),
}
V5_SECURITY_EXTENSION_COMMIT = "f722db2ad9abd75c421b46d3015d50aa57ef77bf"
V5_SECURITY_EXTENSION_STATUS = (
    "model_event_composition_proved_deployed_mapping_and_probability_bounds_open"
)
V5_SECURITY_EXTENSION_PAGE = (
    "docs/reviews/v5-formal-security-extension-20260814.html"
)
V5_SECURITY_EXTENSION_THEOREMS = {
    "conditional_false_accept_work_normalized_bound": (
        "AspisV5DeployedFalseAcceptance."
        "conditional_deployed_false_accept_work_normalized_le"
    ),
    "conditional_false_accept_raw_bound": (
        "AspisV5DeployedFalseAcceptance."
        "conditional_deployed_false_accept_raw_le_min"
    ),
    "same_position_merkle_collision_reduction": (
        "AspisApplicationMerkleBinding."
        "same_position_different_leaf_same_root_exposes_node_collision"
    ),
    "fixed_victim_eight_event_bound": (
        "AspisV5FixedVictimTheftGame.deployed_attack_measure_le_eight_failures"
    ),
}
V5_SECURITY_EXTENSION_THEOREM_SOURCE_PATHS = {
    "conditional_false_accept_work_normalized_bound": (
        "AspisFormal/AspisFormal/V5DeployedFalseAcceptance.lean"
    ),
    "conditional_false_accept_raw_bound": (
        "AspisFormal/AspisFormal/V5DeployedFalseAcceptance.lean"
    ),
    "same_position_merkle_collision_reduction": (
        "AspisFormal/AspisFormal/ApplicationMerkleBinding.lean"
    ),
    "fixed_victim_eight_event_bound": (
        "AspisFormal/AspisFormal/V5FixedVictimTheftGame.lean"
    ),
}
V5_SECURITY_EXTENSION_REMAINING_BOUNDARY_KINDS = (
    "parameterized_failure_predicates_to_deployed_selector_branches",
    "exact_deployed_tag67_to_protocol_acceptance",
    "accepted_tag67_to_normalized_trace_and_public_state",
    "pcs_fri_fiat_shamir_branch_bounds",
    "tag67_transcript_hash_and_separate_output_grinding_applicability",
    "rust_sampling_challenge_order_and_transcript_correspondence",
    "adaptive_experiment_and_query_budget_interpretation",
    "deployed_poseidon2_faithfulness_and_primitive_security",
    "deployed_multi_proof_extraction",
    "fixed_victim_credential_target_sampling_setup_and_concrete_bounds",
    "pda_and_solana_runtime_assumptions",
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


def require_repository_file(path_value: str, label: str) -> Path:
    require(isinstance(path_value, str) and path_value, f"{label}: path is not a string")
    require("\x00" not in path_value, f"{label}: path contains NUL")
    require("\\" not in path_value, f"{label}: path must use repository separators")
    relative = Path(path_value)
    require(not relative.is_absolute(), f"{label}: path must be repository-relative")
    require(
        relative.as_posix() == path_value and all(part not in (".", "..") for part in relative.parts),
        f"{label}: path is not normalized",
    )
    path = ROOT / relative
    resolved = path.resolve()
    require(
        resolved == ROOT.resolve() or ROOT.resolve() in resolved.parents,
        f"{label}: path escapes the repository",
    )
    require(path.is_file(), f"{label}: file is missing at {path_value}")
    return path


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


def git_blob(commit: str, path_value: str) -> bytes:
    result = subprocess.run(
        ["git", "cat-file", "blob", f"{commit}:{path_value}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise AssertionError(
            f"git cannot read {path_value!r} at source commit {commit}: {detail}"
        )
    return result.stdout


def require_git_commit(commit: str, label: str) -> None:
    require(
        isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
        f"{label}: expected a full lowercase Git commit",
    )
    require_equal(
        git_output("rev-parse", "--verify", f"{commit}^{{commit}}"),
        commit,
        label,
    )


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


def check_formal_artifacts(
    artifacts: dict[str, Any],
    required_paths: set[str],
    label: str,
    *,
    exact_paths: bool = False,
    pinned_source_commit: str | None = None,
) -> None:
    require(isinstance(artifacts, dict) and artifacts, f"{label} artifacts are empty")
    if exact_paths:
        require_equal(set(artifacts), required_paths, f"{label} artifact paths")
    else:
        require(
            required_paths.issubset(artifacts),
            f"{label} omits a required theorem or replay artifact",
        )

    for path_value, identity in artifacts.items():
        require(
            isinstance(identity, dict),
            f"{label} artifact {path_value!r}: identity is not an object",
        )
        require_equal(
            set(identity),
            {"bytes", "sha256", "source_commit"},
            f"{label} artifact {path_value!r} identity fields",
        )
        require(
            type(identity["bytes"]) is int and identity["bytes"] >= 0,
            f"{label} artifact {path_value!r}: invalid byte length",
        )
        require(
            isinstance(identity["sha256"], str)
            and re.fullmatch(r"[0-9a-f]{64}", identity["sha256"]) is not None,
            f"{label} artifact {path_value!r}: invalid SHA-256",
        )
        require_repository_file(path_value, f"{label} artifact {path_value!r}")
        require_file_identity(path_value, identity["bytes"], identity["sha256"])
        if pinned_source_commit is not None:
            require_equal(
                identity["source_commit"],
                pinned_source_commit,
                f"{label} artifact {path_value!r} source commit",
            )
        require_git_commit(
            identity["source_commit"],
            f"{label} artifact {path_value!r} source commit",
        )
        committed_source = git_blob(identity["source_commit"], path_value)
        require_equal(
            len(committed_source),
            identity["bytes"],
            f"{label} artifact {path_value!r} source-commit byte length",
        )
        require_equal(
            hashlib.sha256(committed_source).hexdigest(),
            identity["sha256"],
            f"{label} artifact {path_value!r} source-commit SHA-256",
        )


def check_v5_formal_evidence(
    facts: dict[str, Any],
    mainnet_manifest: dict[str, Any],
) -> None:
    sources = facts["authoritative_sources"]
    formal = facts["formal"]
    mainnet = facts["mainnet"]
    program = facts["program"]

    require_equal(
        set(formal),
        {
            "evidence_path",
            "maintained_lean_project_commit",
            "lean_toolchain",
            "lean_status_page",
            "aeneas_status_page",
            "aeneas_commit",
            "charon_commit",
            "principal_integration_theorem",
            "coverage_status",
            "tag67_work_theorem_boundary",
            "post_release_formal_review",
            "post_review_security_extension",
        },
        "V5 formal fact fields",
    )
    require_equal(
        sources["formal_evidence"],
        formal["evidence_path"],
        "V5 authoritative formal-evidence path",
    )
    require_equal(
        formal["evidence_path"],
        V5_FORMAL_EVIDENCE_PATH,
        "V5 formal-evidence release path",
    )
    require_equal(
        formal["lean_status_page"],
        "AspisFormal/README.md",
        "V5 Lean status-page release path",
    )
    require_equal(
        formal["aeneas_status_page"],
        "aeneas-verif/README.md",
        "V5 Aeneas status-page release path",
    )
    formal_evidence_path = require_repository_file(
        formal["evidence_path"],
        "V5 formal evidence",
    )
    formal_evidence = load_json(formal_evidence_path)

    require_equal(
        set(formal_evidence),
        {
            "artifact",
            "schema_version",
            "release_id",
            "release_tag",
            "release_scope",
            "lean",
            "rust_to_lean",
            "coverage",
            "coverage_status",
            "tag67_work_theorem_boundary",
            "outside_current_proof_scope",
            "replay_commands",
            "post_release_formal_review",
            "artifacts",
        },
        "V5 formal-evidence fields",
    )
    require_equal(
        formal_evidence["artifact"],
        "aspis_v5_tag67_formal_evidence",
        "V5 formal-evidence artifact",
    )
    require_equal(formal_evidence["schema_version"], 2, "V5 formal-evidence schema")
    require_equal(formal_evidence["release_id"], facts["release_id"], "V5 formal release")
    require_equal(
        formal_evidence["release_tag"],
        facts["release_tag"],
        "V5 formal release tag",
    )

    release_scope = formal_evidence["release_scope"]
    require_equal(
        set(release_scope),
        {
            "network",
            "program_id",
            "sbf_sha256",
            "tag67_signature",
            "tag67_finalized_slot",
        },
        "V5 formal release-scope fields",
    )
    require_equal(
        release_scope["network"],
        mainnet_manifest["network"],
        "V5 formal network",
    )
    require_equal(
        release_scope["program_id"],
        mainnet_manifest["mainnet"]["program_id"],
        "V5 formal program manifest binding",
    )
    require_equal(release_scope["program_id"], mainnet["program_id"], "V5 formal program")
    require_equal(
        release_scope["sbf_sha256"],
        mainnet_manifest["frozen_candidate"]["sbf_sha256"],
        "V5 formal SBF manifest binding",
    )
    require_equal(release_scope["sbf_sha256"], program["sbf_sha256"], "V5 formal SBF")
    require_equal(
        release_scope["tag67_signature"],
        mainnet_manifest["mainnet"]["tag67_signature"],
        "V5 formal transaction manifest binding",
    )
    require_equal(
        release_scope["tag67_signature"],
        mainnet["transaction"]["signature"],
        "V5 formal transaction",
    )
    require_equal(
        release_scope["tag67_finalized_slot"],
        mainnet_manifest["mainnet"]["tag67_finalized_slot"],
        "V5 formal slot manifest binding",
    )
    require_equal(
        release_scope["tag67_finalized_slot"],
        mainnet["transaction"]["slot"],
        "V5 formal finalized slot",
    )

    lean = formal_evidence["lean"]
    require_equal(
        lean["maintained_project_commit"],
        formal["maintained_lean_project_commit"],
        "V5 maintained Lean commit",
    )
    require_git_commit(
        formal["maintained_lean_project_commit"],
        "V5 maintained Lean project commit",
    )
    require_equal(lean["toolchain"], formal["lean_toolchain"], "V5 Lean toolchain")
    require_equal(
        formal["lean_toolchain"],
        "leanprover/lean4:v4.32.0",
        "V5 release Lean toolchain",
    )
    require_equal(
        (ROOT / "AspisFormal/lean-toolchain").read_text(encoding="utf-8").strip(),
        formal["lean_toolchain"],
        "V5 maintained Lean toolchain file",
    )
    committed_toolchain = git_blob(
        formal["maintained_lean_project_commit"],
        "AspisFormal/lean-toolchain",
    )
    require_equal(
        committed_toolchain.decode("utf-8").strip(),
        formal["lean_toolchain"],
        "V5 recorded Lean commit toolchain",
    )
    require_equal(lean["status_page"], formal["lean_status_page"], "V5 Lean status page")
    require_equal(
        lean["audited_integration_theorem_dependencies"],
        ["propext", "Classical.choice", "Quot.sound"],
        "V5 audited theorem dependencies",
    )
    require_equal(
        lean["status_assertions"],
        {
            "contains_sorry": False,
            "contains_custom_axiom": False,
            "uses_native_decide": False,
            "uses_compiled_evaluation_shortcut": False,
        },
        "V5 Lean status assertions",
    )

    rust_to_lean = formal_evidence["rust_to_lean"]
    require_equal(
        rust_to_lean["technical_status_page"],
        formal["aeneas_status_page"],
        "V5 Aeneas status page",
    )
    require_equal(
        rust_to_lean["aeneas_commit"],
        formal["aeneas_commit"],
        "V5 Aeneas tool commit",
    )
    require_equal(
        rust_to_lean["charon_commit"],
        formal["charon_commit"],
        "V5 Charon tool commit",
    )
    for tool_name in ("aeneas", "charon"):
        require(
            re.fullmatch(r"[0-9a-f]{40}", formal[f"{tool_name}_commit"]) is not None,
            f"V5 {tool_name} commit is not a full lowercase commit",
        )
    require_equal(
        rust_to_lean["principal_integration_theorem"],
        formal["principal_integration_theorem"],
        "V5 principal integration theorem",
    )
    require_equal(
        formal["principal_integration_theorem"],
        V5_PRINCIPAL_INTEGRATION_THEOREM,
        "V5 release principal integration theorem",
    )
    require_equal(
        formal_evidence["coverage"],
        list(V5_FORMAL_COVERAGE),
        "V5 formal coverage",
    )
    require_equal(
        formal_evidence["coverage_status"],
        V5_FORMAL_COVERAGE_STATUS,
        "V5 formal coverage status",
    )
    require_equal(
        formal["coverage_status"],
        V5_FORMAL_COVERAGE_STATUS,
        "V5 release formal coverage status",
    )
    require_equal(
        formal_evidence["replay_commands"],
        list(V5_FORMAL_REPLAY_COMMANDS),
        "V5 formal replay commands",
    )

    boundary = formal_evidence["tag67_work_theorem_boundary"]
    require_equal(
        boundary["kind"],
        formal["tag67_work_theorem_boundary"],
        "V5 Tag-67 work-theorem boundary",
    )
    require_equal(
        formal["tag67_work_theorem_boundary"],
        V5_TAG67_WORK_THEOREM_BOUNDARY,
        "V5 release Tag-67 work-theorem boundary",
    )
    require_equal(
        boundary["statement"],
        V5_TAG67_WORK_THEOREM_BOUNDARY_STATEMENT,
        "V5 Tag-67 work-theorem boundary statement",
    )
    require(
        isinstance(boundary["explanation"], str) and boundary["explanation"],
        "V5 Tag-67 work-theorem boundary explanation is empty",
    )
    require(
        "only" in boundary["explanation"].lower()
        and "not" in boundary["explanation"].lower(),
        "V5 Tag-67 boundary must say that it is not the only global assumption",
    )

    review = formal_evidence["post_release_formal_review"]
    require_equal(
        set(review),
        {
            "date",
            "commit",
            "status",
            "review_page",
            "theorems",
            "remaining_boundaries",
            "replay_command",
            "artifacts",
        },
        "V5 post-release formal-review fields",
    )
    require_equal(review["date"], V5_POST_RELEASE_REVIEW_DATE, "V5 review date")
    require_equal(
        review["commit"],
        V5_POST_RELEASE_REVIEW_COMMIT,
        "V5 review commit",
    )
    require_git_commit(review["commit"], "V5 post-release formal-review commit")
    require_equal(
        review["status"],
        V5_POST_RELEASE_REVIEW_STATUS,
        "V5 post-release formal-review status",
    )
    require_equal(
        review["review_page"],
        V5_POST_RELEASE_REVIEW_PAGE,
        "V5 post-release formal-review page",
    )
    require_repository_file(review["review_page"], "V5 post-release review page")
    require_equal(
        review["theorems"],
        V5_POST_RELEASE_REVIEW_THEOREMS,
        "V5 post-release formal-review theorems",
    )
    boundaries = review["remaining_boundaries"]
    require(
        isinstance(boundaries, list),
        "V5 post-release remaining boundaries are not a list",
    )
    for index, item in enumerate(boundaries):
        require(
            isinstance(item, dict),
            f"V5 post-release remaining boundary {index} is not an object",
        )
        require_equal(
            set(item),
            {"kind", "explanation"},
            f"V5 post-release remaining boundary {index} fields",
        )
        require(
            isinstance(item["explanation"], str) and item["explanation"],
            f"V5 post-release remaining boundary {index} explanation is empty",
        )
    boundary_kinds = [item["kind"] for item in boundaries]
    require_equal(
        boundary_kinds,
        list(V5_POST_RELEASE_REMAINING_BOUNDARY_KINDS),
        "V5 post-release remaining boundary kinds",
    )
    require_equal(
        len(boundary_kinds),
        len(set(boundary_kinds)),
        "V5 post-release remaining boundary uniqueness",
    )
    require_equal(
        review["replay_command"],
        V5_POST_RELEASE_REPLAY_COMMAND,
        "V5 post-release formal-review replay command",
    )

    review_facts = formal["post_release_formal_review"]
    require_equal(
        set(review_facts),
        {
            "date",
            "commit",
            "status",
            "review_page",
            "theorems",
            "remaining_boundary_kinds",
        },
        "V5 post-release formal-review fact fields",
    )
    require_equal(review_facts["date"], review["date"], "V5 review fact date")
    require_equal(review_facts["commit"], review["commit"], "V5 review fact commit")
    require_equal(review_facts["status"], review["status"], "V5 review fact status")
    require_equal(
        review_facts["review_page"],
        review["review_page"],
        "V5 review fact page",
    )
    require_equal(
        review_facts["theorems"],
        review["theorems"],
        "V5 review fact theorems",
    )
    require_equal(
        review_facts["remaining_boundary_kinds"],
        boundary_kinds,
        "V5 review fact remaining boundary kinds",
    )

    extension = formal["post_review_security_extension"]
    require_equal(
        set(extension),
        {
            "date",
            "commit",
            "status",
            "review_page",
            "theorems",
            "conditional_probability_statement",
            "remaining_boundary_kinds",
        },
        "V5 security-extension fact fields",
    )
    require_equal(extension["date"], V5_POST_RELEASE_REVIEW_DATE, "V5 extension date")
    require_equal(
        extension["commit"],
        V5_SECURITY_EXTENSION_COMMIT,
        "V5 security-extension commit",
    )
    require_git_commit(extension["commit"], "V5 security-extension commit")
    require_equal(
        extension["status"],
        V5_SECURITY_EXTENSION_STATUS,
        "V5 security-extension status",
    )
    require_equal(
        extension["review_page"],
        V5_SECURITY_EXTENSION_PAGE,
        "V5 security-extension review page",
    )
    require_repository_file(extension["review_page"], "V5 security-extension page")
    require_equal(
        git_output("ls-files", "--error-unmatch", "--", extension["review_page"]),
        extension["review_page"],
        "V5 security-extension tracked review page",
    )
    require_equal(
        extension["theorems"],
        V5_SECURITY_EXTENSION_THEOREMS,
        "V5 security-extension theorems",
    )
    require_equal(
        extension["conditional_probability_statement"],
        {
            "query_budget_min": 1,
            "query_budget_max_power_of_two": 128,
            "work_normalized_upper_bound": "2^-100",
            "ordinary_upper_bound": "min(1,T/2^100)",
        },
        "V5 security-extension conditional probability statement",
    )
    require_equal(
        extension["remaining_boundary_kinds"],
        list(V5_SECURITY_EXTENSION_REMAINING_BOUNDARY_KINDS),
        "V5 security-extension remaining boundaries",
    )
    for theorem_label, theorem_name in V5_SECURITY_EXTENSION_THEOREMS.items():
        source_path = V5_SECURITY_EXTENSION_THEOREM_SOURCE_PATHS[theorem_label]
        source = git_blob(extension["commit"], source_path).decode("utf-8")
        short_name = theorem_name.rsplit(".", 1)[1]
        require(
            re.search(rf"\btheorem\s+{re.escape(short_name)}\b", source) is not None,
            f"V5 security-extension theorem {theorem_name!r} is absent at the commit",
        )

    for theorem_label, theorem_name in V5_POST_RELEASE_REVIEW_THEOREMS.items():
        source_path = V5_POST_RELEASE_THEOREM_SOURCE_PATHS[theorem_label]
        source = git_blob(review["commit"], source_path).decode("utf-8")
        short_name = theorem_name.rsplit(".", 1)[1]
        require(
            re.search(rf"\btheorem\s+{re.escape(short_name)}\b", source) is not None,
            f"V5 post-release theorem {theorem_name!r} is absent at the review commit",
        )

    for status_label, status_path in (
        ("Lean", formal["lean_status_page"]),
        ("Aeneas", formal["aeneas_status_page"]),
    ):
        require_repository_file(status_path, f"V5 {status_label} status page")
        require_literals(
            status_path,
            [formal["principal_integration_theorem"]],
        )
    require_literals(
        formal["aeneas_status_page"],
        [formal["aeneas_commit"], formal["charon_commit"]],
    )

    check_formal_artifacts(
        formal_evidence["artifacts"],
        V5_REQUIRED_FORMAL_ARTIFACTS,
        "V5 release-time formal evidence",
    )
    check_formal_artifacts(
        review["artifacts"],
        V5_REQUIRED_POST_RELEASE_REVIEW_ARTIFACTS,
        "V5 post-release formal review",
        exact_paths=True,
        pinned_source_commit=review["commit"],
    )

    release_prefix = f"release/{facts['release_id']}/"
    require(
        formal["evidence_path"].startswith(release_prefix),
        "V5 formal evidence is outside the mainnet release bundle",
    )
    formal_manifest_path = formal["evidence_path"][len(release_prefix) :]
    require_equal(
        formal_manifest_path,
        "formal/formal-evidence.json",
        "V5 formal manifest object path",
    )
    require(
        formal_manifest_path in mainnet_manifest["objects"],
        "V5 mainnet manifest omits formal evidence",
    )
    manifest_identity = mainnet_manifest["objects"][formal_manifest_path]
    require_equal(
        manifest_identity["bytes"],
        formal_evidence_path.stat().st_size,
        "V5 formal manifest byte length",
    )
    require_equal(
        manifest_identity["sha256"],
        sha256(formal_evidence_path),
        "V5 formal manifest SHA-256",
    )


def check_v5(facts: dict[str, Any], compute_limit: int) -> None:
    require_equal(facts["role"], "finalized_mainnet_release", "V5 role")
    require_equal(facts["status"], "finalized_mainnet", "V5 status")
    require_equal(facts["release_id"], "aspis-v5-tag67-mainnet-v1", "V5 release id")
    require_equal(facts["release_tag"], facts["release_id"], "V5 release tag name")
    require_equal(
        tag_commit(facts["release_tag"]),
        facts["release_tag_commit"],
        "V5 release tag commit",
    )
    require_equal(
        object_tree(facts["release_tag"]),
        facts["release_tag_tree"],
        "V5 release tag tree",
    )
    require_equal(
        facts["mainnet"]["deployment_status"],
        "deployed_then_programdata_closed_after_demonstration",
        "V5 deployment status",
    )
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
    manifest = load_json(ROOT / sources["candidate_manifest"])
    mainnet_manifest = load_json(ROOT / sources["mainnet_manifest"])
    mainnet_lifecycle = load_json(ROOT / sources["mainnet_lifecycle"])
    devnet_execution = load_json(ROOT / sources["devnet_execution"])
    frozen_policy = load_json(ROOT / sources["frozen_compute_policy"])
    runtime_path = ROOT / sources["current_runtime_replay"]
    runtime = load_json(runtime_path)
    program = facts["program"]
    proof = facts["proof"]
    devnet = facts["devnet"]
    mainnet = facts["mainnet"]
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
    require_file_identity(proof["path"], proof["bytes"], proof["sha256"])
    require_file_identity(
        proof["statement_path"],
        proof["statement_bytes"],
        proof["statement_sha256"],
    )

    require_equal(
        mainnet_manifest["release_id"],
        facts["release_id"],
        "V5 mainnet manifest release id",
    )
    require_equal(mainnet_manifest["network"], "mainnet-beta", "V5 mainnet network")
    require_equal(
        mainnet_manifest["genesis_hash"],
        mainnet["genesis_hash"],
        "V5 mainnet genesis",
    )
    require_equal(
        mainnet_manifest["frozen_candidate"]["sbf_sha256"],
        program["sbf_sha256"],
        "V5 mainnet manifest SBF hash",
    )
    require_equal(
        mainnet_manifest["frozen_candidate"]["sbf_bytes"],
        program["sbf_bytes"],
        "V5 mainnet manifest SBF bytes",
    )
    require_equal(
        mainnet_manifest["mainnet"]["program_id"],
        mainnet["program_id"],
        "V5 mainnet manifest program",
    )
    require_equal(
        mainnet["program_id"],
        program["declared_id"],
        "V5 deployed/declared program",
    )
    require_equal(
        mainnet_manifest["mainnet"]["tag67_signature"],
        mainnet["transaction"]["signature"],
        "V5 mainnet manifest transaction",
    )
    require_equal(
        mainnet_manifest["mainnet"]["tag67_finalized_slot"],
        mainnet["transaction"]["slot"],
        "V5 mainnet manifest finalized slot",
    )
    require_equal(
        mainnet_manifest["mainnet"]["tag67_compute_units"],
        mainnet["transaction"]["compute_units"],
        "V5 mainnet manifest transaction CU",
    )
    for path_value, identity in mainnet_manifest["objects"].items():
        require_file_identity(
            f"release/{facts['release_id']}/{path_value}",
            identity["bytes"],
            identity["sha256"],
        )
    check_v5_formal_evidence(facts, mainnet_manifest)

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
        facts["compute"]["bump_policy_enforced_by"],
        "mainnet_runner",
        "V5 bump-policy enforcement location",
    )
    bump_policy_source = facts["compute"]["bump_policy_source"]
    require_equal(
        set(bump_policy_source),
        {
            "path",
            "first_guard_commit",
            "pre_execution_artifact_selection_commit",
            "exact_executed_runner_commit_bound_in_immutable_evidence",
        },
        "V5 bump-policy source fields",
    )
    require_equal(
        bump_policy_source["path"],
        "xtask/src/spend_devnet/v5.rs",
        "V5 bump-policy source path",
    )
    require_equal(
        bump_policy_source["first_guard_commit"],
        "86e631316b0555aa883fe2fda96f763a4cb6d20b",
        "V5 bump-policy first guard commit",
    )
    require_git_commit(
        bump_policy_source["first_guard_commit"],
        "V5 bump-policy first guard commit",
    )
    bump_policy_source_text = git_blob(
        bump_policy_source["first_guard_commit"],
        bump_policy_source["path"],
    ).decode("utf-8")
    for literal in (
        "const MAINNET_NULLIFIER_PDA_BUMP: u8 = u8::MAX;",
        "bump == MAINNET_NULLIFIER_PDA_BUMP",
    ):
        require(
            literal in bump_policy_source_text,
            f"V5 recorded runner source omits {literal!r}",
        )
    require_equal(
        bump_policy_source["pre_execution_artifact_selection_commit"],
        "7807193cfcfc1e82f5fb733d4df063b1e5c178a8",
        "V5 bump-policy pre-execution artifact-selection commit",
    )
    require_git_commit(
        bump_policy_source["pre_execution_artifact_selection_commit"],
        "V5 bump-policy pre-execution artifact-selection commit",
    )
    artifact_selection_source = git_blob(
        bump_policy_source["pre_execution_artifact_selection_commit"],
        bump_policy_source["path"],
    ).decode("utf-8")
    require(
        "Some((config.program_id, MAINNET_NULLIFIER_PDA_BUMP))"
        in artifact_selection_source,
        "V5 recorded artifact-builder source omits bump-255 selection",
    )
    require_equal(
        bump_policy_source[
            "exact_executed_runner_commit_bound_in_immutable_evidence"
        ],
        False,
        "V5 exact executed runner commit evidence status",
    )
    require_equal(
        facts["compute"]["landed_nullifier_pda_bump"],
        facts["compute"]["required_nullifier_pda_bump"],
        "V5 landed nullifier PDA bump",
    )
    require_equal(
        facts["compute"]["deployed_program_validated_derived_pda"],
        True,
        "V5 deployed PDA-address validation",
    )
    require_equal(
        facts["compute"]["deployed_program_enforced_specific_bump"],
        False,
        "V5 deployed numeric-bump enforcement",
    )
    require_equal(
        facts["compute"]["later_release_source_required_bump"],
        255,
        "V5 later source bump requirement",
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
    require_equal(
        facts["compute"]["mainnet_simulation_cu"],
        facts["compute"]["mainnet_landed_cu"],
        "V5 mainnet simulation/landing CU",
    )
    require_equal(
        facts["compute"]["mainnet_landed_cu"]
        + facts["compute"]["mainnet_wire_headroom_under_instruction_limit_cu"],
        facts["compute"]["transaction_compute_unit_limit_cu"],
        "V5 landed-wire CU arithmetic",
    )

    require_equal(
        mainnet_lifecycle["artifact"],
        "aspis_v5_tag67_mainnet_lifecycle",
        "V5 mainnet lifecycle artifact",
    )
    require_equal(
        mainnet_lifecycle["genesis_hash"],
        mainnet["genesis_hash"],
        "V5 lifecycle genesis",
    )
    require_equal(
        mainnet_lifecycle["runtime"]["solana_core"],
        mainnet["solana_core"],
        "V5 lifecycle runtime",
    )
    require_equal(
        mainnet_lifecycle["runtime"]["feature_set"],
        mainnet["feature_set"],
        "V5 lifecycle feature set",
    )
    identities = mainnet_lifecycle["identities"]
    require_equal(identities["program"], mainnet["program_id"], "V5 mainnet program")
    require_equal(identities["pool"], mainnet["pool"], "V5 mainnet pool")
    require_equal(
        identities["proof_account"],
        mainnet["proof_account"],
        "V5 mainnet proof account",
    )
    require_equal(identities["nullifier"], mainnet["nullifier"], "V5 mainnet nullifier")
    require_equal(
        identities["nullifier_pda_bump"],
        mainnet["nullifier_pda_bump"],
        "V5 mainnet nullifier bump",
    )
    require_equal(
        mainnet_lifecycle["artifacts"]["sbf"]["sha256"],
        program["sbf_sha256"],
        "V5 lifecycle SBF hash",
    )
    require_equal(
        mainnet_lifecycle["artifacts"]["proof"]["sha256"],
        proof["sha256"],
        "V5 lifecycle proof hash",
    )
    require_equal(
        mainnet_lifecycle["artifacts"]["statement"]["sha256"],
        proof["statement_sha256"],
        "V5 lifecycle statement hash",
    )

    transactions = mainnet_lifecycle["transactions"]
    for ledger_name, evidence_name in (
        ("deployment_transaction", "deployment"),
        ("transaction", "tag67"),
        ("proof_close", "proof_close_tag64"),
        ("programdata_close", "programdata_close"),
        ("payer_sweep", "payer_sweep"),
    ):
        ledger_transaction = mainnet[ledger_name]
        evidence_transaction = transactions[evidence_name]
        require_equal(
            evidence_transaction["signature"],
            ledger_transaction["signature"],
            f"V5 {evidence_name} signature",
        )
        require_equal(
            evidence_transaction["finalized_slot"],
            ledger_transaction["slot"],
            f"V5 {evidence_name} slot",
        )
        require(evidence_transaction["finalized_success"], f"V5 {evidence_name} did not finalize")
    require_equal(
        transactions["tag67"]["simulation_compute_units"],
        mainnet["transaction"]["simulation_compute_units"],
        "V5 Tag-67 simulation CU",
    )
    require_equal(
        transactions["tag67"]["landed_compute_units"],
        mainnet["transaction"]["compute_units"],
        "V5 Tag-67 landed CU",
    )
    require_equal(
        transactions["tag67"]["wire_sha256"],
        mainnet["transaction"]["wire_sha256"],
        "V5 Tag-67 wire hash",
    )
    require_equal(
        mainnet_lifecycle["transaction_accounting"]["core_lifecycle_transactions"],
        mainnet["transaction_accounting"]["core_lifecycle_total"],
        "V5 core lifecycle transaction count",
    )
    require_equal(
        mainnet_lifecycle["refund_reconciliation"][
            "total_direct_receipt_by_pinned_recipient_lamports"
        ],
        mainnet["refund"]["direct_receipt_lamports"],
        "V5 pinned refund total",
    )
    require_equal(
        transactions["programdata_close"]["refund_direct_to_pinned_recipient_lamports"]
        + transactions["payer_sweep"]["transfer_to_pinned_recipient_lamports"],
        mainnet["refund"]["direct_receipt_lamports"],
        "V5 direct refund arithmetic",
    )
    require_equal(
        mainnet_lifecycle["retained_accounts"]["total_permanent_lamports"],
        mainnet["retained_rent_lamports"]["total"],
        "V5 retained-rent total",
    )
    require_equal(
        mainnet["retained_rent_lamports"]["program"]
        + mainnet["retained_rent_lamports"]["pool"]
        + mainnet["retained_rent_lamports"]["nullifier"],
        mainnet["retained_rent_lamports"]["total"],
        "V5 retained-rent arithmetic",
    )
    require_literals(
        "xtask/src/spend_devnet/v5.rs",
        [
            "const MAINNET_NULLIFIER_PDA_BUMP: u8 = aspis_verifier::v5_full_transaction::V5_NULLIFIER_PDA_BUMP;",
            "const MAINNET_RELEASE_POLICY_CU_CEILING: u64 = 1_356_912;",
            "ComputeBudgetInstruction::set_compute_unit_limit(tag67_compute_unit_limit)",
            "units <= u64::from(tag67_compute_unit_limit)",
            "final_transaction_landed_cu <= u64::from(tag67_compute_unit_limit)",
        ],
    )
    require_literals(
        "programs/aspis-verifier/src/v5_full_transaction.rs",
        ["pub const V5_NULLIFIER_PDA_BUMP: u8 = u8::MAX;"],
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
    v5 = facts["tracks"]["v5_tag67_mainnet_v1"]
    formal_evidence = load_json(ROOT / v5["authoritative_sources"]["formal_evidence"])
    require_literals(
        "README.md",
        [
            q18["mainnet"]["transaction"]["signature"],
            f"{q18['compute']['measured_transaction_cu']:,}",
            v5["mainnet"]["transaction"]["signature"],
            str(v5["mainnet"]["transaction"]["slot"]),
            f"{v5['compute']['mainnet_landed_cu']:,}",
            v5["mainnet"]["program_id"],
            f"{v5['proof']['bytes']:,}",
            f"{v5['program']['sbf_bytes']:,}",
            v5["program"]["sbf_sha256"],
            "docs/formal-verification.md",
            "docs/assumptions-ledger.md",
            "docs/v5-mainnet-demo.md",
            "release/aspis-v5-tag67-frozen-candidate-v1/",
            "release/aspis-v5-tag67-mainnet-v1/",
            "AspisFormal/",
            "aeneas-verif/",
            V5_POST_RELEASE_REVIEW_PAGE,
            "cd AspisFormal",
            "lake exe cache get",
            "lake build",
            formal_evidence["replay_commands"][1],
            formal_evidence["replay_commands"][2],
            "./release/aspis-v5-tag67-frozen-candidate-v1/verify.sh",
            "./release/aspis-v5-tag67-mainnet-v1/verify.sh",
            "python3 tools/check_release_facts.py",
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
        "docs/v5-mainnet-demo.md",
        [
            v5["mainnet"]["deployment_transaction"]["signature"],
            v5["mainnet"]["transaction"]["signature"],
            str(v5["mainnet"]["transaction"]["slot"]),
            f"{v5['compute']['mainnet_landed_cu']:,}",
            v5["mainnet"]["proof_close"]["signature"],
            v5["mainnet"]["programdata_close"]["signature"],
            v5["mainnet"]["payer_sweep"]["signature"],
            v5["mainnet"]["refund"]["recipient"],
            f"{v5['mainnet']['refund']['direct_receipt_lamports']:,}",
            "84",
            "71",
            "../release/aspis-v5-tag67-mainnet-v1/verify.sh",
        ],
    )
    require_literals(
        "release/preflight/v5-production-freeze.md",
        [
            v5["mainnet"]["transaction"]["signature"],
            v5["program"]["sbf_sha256"],
            f"{v5['compute']['mainnet_landed_cu']:,}",
            "nullifier PDA bump was exactly\n`255`",
            "exact signed-wire\nsimulation",
            v5["mainnet"]["refund"]["recipient"],
        ],
    )
    require_literals(
        "paper/aspis-spend/sections/formalization.tex",
        [v5["mainnet"]["transaction"]["signature"]],
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
    )
    for example in stale_examples:
        require(stale_claims(path, example), f"self-test did not reject {example!r}")
    clean = (
        "V5 finalized on mainnet. The recorded runner policy required an exact "
        "signed-wire simulation at or below 1,356,912 CU. The landed wire "
        "consumed 1,334,452 CU with observed bump 255."
    )
    require(not stale_claims(path, clean), "self-test rejected the current release statement")
    print("PASS: release-facts stale-claim self-test")


def check() -> None:
    facts = load_json(LEDGER_PATH)
    require_equal(facts["artifact"], "aspis_release_facts", "ledger artifact")
    require_equal(facts["schema_version"], 4, "ledger schema version")
    require(
        re.fullmatch(r"\d{4}-\d{2}-\d{2}", facts["facts_as_of_date"]) is not None,
        "facts_as_of_date must use YYYY-MM-DD",
    )
    require_equal(
        facts["facts_as_of_date"],
        V5_POST_RELEASE_REVIEW_DATE,
        "release facts date",
    )
    compute_limit = facts["transaction_compute_limit_cu"]
    require_equal(compute_limit, 1_400_000, "transaction CU limit")
    tracks = facts["tracks"]
    require_equal(
        set(tracks),
        {"q18_g37_tag65_mainnet_v1", "v5_tag67_mainnet_v1"},
        "release track set",
    )
    check_q18(tracks["q18_g37_tag65_mainnet_v1"], compute_limit)
    check_v5(tracks["v5_tag67_mainnet_v1"], compute_limit)
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
