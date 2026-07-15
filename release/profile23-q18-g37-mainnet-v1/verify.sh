#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

fail() {
  printf 'FAIL: %s\n' "$*" >&2
  exit 1
}

command -v jq >/dev/null 2>&1 || fail "jq is required"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    fail "sha256sum or shasum is required"
  fi
}

sha256_stream() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  else
    fail "sha256sum or shasum is required"
  fi
}

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c SHA256SUMS
else
  shasum -a 256 -c SHA256SUMS
fi

diff -u \
  <(awk '{print $2}' SHA256SUMS | sort) \
  <(find . -type f ! -name SHA256SUMS -print | sed 's#^\./##' | sort) \
  >/dev/null || fail "SHA256SUMS does not enumerate every bundle file exactly once"

jq -r '.objects | to_entries[] | [.key, (.value.bytes | tostring), .value.sha256] | @tsv' manifest.json |
while IFS=$'\t' read -r path expected_bytes expected_sha256; do
  [[ -f "$path" ]] || fail "manifest object is missing: $path"
  actual_bytes=$(wc -c < "$path" | tr -d '[:space:]')
  [[ "$actual_bytes" == "$expected_bytes" ]] ||
    fail "$path has $actual_bytes bytes; expected $expected_bytes"
  [[ "$(sha256_file "$path")" == "$expected_sha256" ]] ||
    fail "$path has an unexpected SHA-256"
done

proof_header=$(od -An -tx1 -N16 proof/profile23-q18-g37.bin | tr -d '[:space:]')
[[ "$proof_header" == "4153503004170a09120020000204020b" ]] || fail "unexpected proof header"

elf_header=$(od -An -tx1 -N4 program/aspis_verifier.so | tr -d '[:space:]')
[[ "$elf_header" == "7f454c46" ]] || fail "SBF artifact is not an ELF image"

programdata_bytes=$((45 + $(wc -c < program/aspis_verifier.so)))
[[ "$programdata_bytes" == "921893" ]] || fail "reconstructed ProgramData has an unexpected length"
programdata_sha256=$(
  {
    printf '%b' '\x03\x00\x00\x00\x4e\x0a\xce\x19\x00\x00\x00\x00\x01\x0b\x9b\xed\x66\xbc\xbf\xab\x08\x94\x3d\x91\x28\x4f\x2c\x94\x2d\x4e\x6b\xa9\x2b\x37\xe6\x68\xe4\xd4\x10\xb9\x99\x8c\xdb\x95\x60'
    cat program/aspis_verifier.so
  } | sha256_stream
)
[[ "$programdata_sha256" == "7fe4c7352f19ed00a3ba72b3dc6038943db3e5311c23cd5c1b0f8dbb15c4cda2" ]] ||
  fail "release SBF does not reconstruct the finalized ProgramData image"

pdf_header=$(od -An -tc -N4 paper/profile23.pdf | tr -d '[:space:]')
[[ "$pdf_header" == "%PDF" ]] || fail "paper artifact is not a PDF"

jq -e '
  .schema_version == 1 and
  .artifact == "aspis_profile23_q18_g37_mainnet_publication_bundle" and
  .release_id == "profile23-q18-g37-mainnet-v1" and
  .created_at_utc == "2026-07-15T06:48:33Z" and
  .network == "mainnet-beta" and
  .mainnet_genesis_hash == "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d" and
  .certificate_lineage.publication_certificate_sha256 == "4ace42c0954bee74382520bbb0818da86e570ec9b212c61cb21130dc644a2725" and
  .certificate_lineage.execution_time_certificate_sha256 == "d83f6df645a00f28090e78f8648974ec94afd35f4677f5d84525ba6af7a2688f" and
  .certificate_lineage.substantive_release_fields_identical == true and
  .readiness_lineage.publication_preflight_sha256 == "be9d5344a29befaf24af5483a2187250e6793908f832efe957477645469ae480" and
  .readiness_lineage.execution_time_preflight_sha256 == "463c82a484d27bff3f6d616f94137860339f8be823a74c6f3e22968dc81fe237" and
  .readiness_lineage.publication_schema_clarification_only == true and
  .readiness_lineage.publication_preflight_is_execution_attestation == false and
  .profile.queries == 18 and
  .profile.batch_grinding_bits == 37 and
  .profile.release_gates_passed == 36 and
  .profile.release_gates_total == 36 and
  .profile.conservative_soundness_floor_bits == 100.16144938287457 and
  .release_instance.proof_bytes == 64447 and
  .release_instance.proof_sha256 == "d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d" and
  .release_instance.statement_bytes == 667 and
  .release_instance.statement_sha256 == "947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2" and
  .release_instance.sbf_bytes == 921848 and
  .release_instance.sbf_sha256 == "97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a" and
  .mainnet.verification_signature == "4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo" and
  .mainnet.verification_finalized_slot == 432933949 and
  .mainnet.verification_block_time_unix == 1784065236 and
  .mainnet.verification_compute_units == 1343749 and
  .mainnet.returned_lamports == 6985137600 and
  .mainnet.final_payer_lamports == 0 and
  .mainnet.nonrefundable_lamports == 14883400 and
  .publication_transform.derived_public_evidence == true and
  .publication_transform.cryptographic_hashes_signatures_slots_balances_logs_and_account_images_preserved == true
' manifest.json >/dev/null

jq -e '
  .artifact == "profile23_one_transaction_release" and
  .released == true and
  .status == "released_all_required_gates_green" and
  (.gates | length) == 36 and
  (.gates | all(.passed == true)) and
  (.failed_gates | length) == 0 and
  .coarse_whole_soundness_floor_bits == 100.16144938287457 and
  .max_literal_production_tag65_cu == 1340803 and
  .exact_headroom_under_1_4m_cu == 59197 and
  .proof.bytes == 64447 and
  .proof.sha256 == "d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d" and
  .release_instance.statement_bytes == 667 and
  .release_instance.statement_sha256 == "947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2" and
  .release_instance.statement_sequence == 0 and
  .release_instance.serialized_selector == 0 and
  .release_instance.least_good_selector == 0 and
  .release_instance.production_host_verification_green == true and
  .default_production_sbf.bytes == 921848 and
  .default_production_sbf.sha256 == "97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a"
' certificates/release.json >/dev/null

jq -n -e \
  --slurpfile publication certificates/release.json \
  --slurpfile execution certificates/release-execution-time.json \
  --arg publication_note "Concrete-proof KAT fields under the static HVZK artifact's complete_public_view object are non-authorizing regression metadata; production_release explicitly omits duplicated concrete identities, and neither object can authorize this release instance." \
  --arg execution_note "Historical concrete-proof fields under the static HVZK artifact's complete_public_view and production_release objects are retained only as non-authorizing regression metadata; they are not theorem assumptions and cannot authorize this release instance." '
    def normalized:
      del(.generated_at_utc, .notes[3]) |
      .source_artifacts |= map(
        if (.label == "acceptance" or .label == "mutation" or .label == "soundness" or
            .label == "complete_good" or .label == "computational_hvzk") then
          del(.bytes, .sha256)
        elif .label == "program_manifest" then
          del(.sha256)
        else . end
      );
    ($publication[0]) as $p | ($execution[0]) as $e |
    ($p | normalized) == ($e | normalized) and
    ([$p.source_artifacts[] | select(.label == "soundness")][0] |
      .bytes == 11001 and
      .sha256 == "a5a77e5d858769f10e032ced3a7ecc76e7c616f7395b4a3d8df9f9f75f7452ab") and
    ([$p.source_artifacts[] | select(.label == "acceptance")][0] |
      .bytes == 4618 and
      .sha256 == "60566e10cf87ce4ebf92bc84fc1cf442ee3b6df82ff61911d95d193ee6521f80") and
    ([$p.source_artifacts[] | select(.label == "mutation")][0] |
      .bytes == 18763 and
      .sha256 == "8e78fb4f089d6097f7748fb20bb5df72fa49a0b1e31ea6eb57deb398511a10ec") and
    ([$p.source_artifacts[] | select(.label == "complete_good")][0] |
      .bytes == 3491 and
      .sha256 == "773e95b24e6af156dd47206aba50bc5efc65a98cb4a4fe7c932f28cef56cb17d") and
    ([$p.source_artifacts[] | select(.label == "computational_hvzk")][0] |
      .bytes == 7762 and
      .sha256 == "376f506d476f3e8949d04db6ba2d2ac40307bf8f28cfa36411244ae2274e574e") and
    ([$p.source_artifacts[] | select(.label == "program_manifest")][0] |
      .sha256 == "72ccd5d630c3710ca2bbfbe23c2f787b98baf9c9b80d58f4659a522e7fd5fb24") and
    ($p.notes[3] == $publication_note) and
    ([$e.source_artifacts[] | select(.label == "soundness")][0] |
      .bytes == 10882 and
      .sha256 == "1cefeee871f5f134a6d046d7b912f3aae14c3e16799bb1619b00ba486a8fcad7") and
    ([$e.source_artifacts[] | select(.label == "acceptance")][0] |
      .bytes == 4653 and
      .sha256 == "084c8e99cb73382b03939ccd4dab5c303d05acc9dcc61fb7bae5f5ddbe742dd9") and
    ([$e.source_artifacts[] | select(.label == "mutation")][0] |
      .bytes == 18798 and
      .sha256 == "b04d33c364cf6e1b3e9ebda3e8b9b80295952cd450ae3c1f09712f39b42c7ecb") and
    ([$e.source_artifacts[] | select(.label == "complete_good")][0] |
      .bytes == 4773 and
      .sha256 == "30d4be7fde6382910ed79503f7f3cbb1b16bace328adcf68a7e8170b878d74a9") and
    ([$e.source_artifacts[] | select(.label == "computational_hvzk")][0] |
      .bytes == 8978 and
      .sha256 == "b577c26205893a9f8857e6994f89b02b86ab9f71266b285a2d77baf32b031055") and
    ([$e.source_artifacts[] | select(.label == "program_manifest")][0] |
      .sha256 == "716d23d087dd2ad320a5a39823357dadcc7d6181036efc8de3e2a31841af54b7") and
    ($e.notes[3] == $execution_note)
  ' >/dev/null

jq -e '
  .artifact == "profile23_mainnet_beta_readiness" and
  .mode == "read_only" and
  .mutations_performed == false and
  .read_only_preflight_green == true and
  .readiness_is_execution_attestation == false and
  (.current_executor_journal_scope | contains("no per-wire persistence")) and
  .required_future_signing_safety_policy.implementation_status == "required_future_contract_not_implemented_by_the_current_top_level_executor" and
  has("required_future_execution_sequence") and
  has("required_future_execution_evidence_fields") and
  (has("execution_sequence") | not) and
  (has("evidence_schema_required_fields") | not) and
  ([.gates[].name] | contains(["top_level_executor_command_registered"])) and
  ([.gates[].name] | contains(["reviewed_live_executor_available"]) | not) and
  (.blockers | length) == 0 and
  .observed_genesis_hash == "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d" and
  .release_certificate_sha256 == "d83f6df645a00f28090e78f8648974ec94afd35f4677f5d84525ba6af7a2688f" and
  .proof_sha256 == "d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d" and
  .certified_statement_sha256 == "947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2" and
  .sbf_sha256 == "97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a" and
  .program_id == "9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z" and
  .certified_pool_address == "B1z4gQ82xerghDKZ68HuP2Tehx5ER5mfVHq74y4ew3kk" and
  .expected_nullifier_address == "2CnUJycxkinN3XtpWH5bCYVDEuMx42BTnFU9WXsymAu3"
' certificates/mainnet-readiness.json >/dev/null

jq -e '
  .artifact == "profile23_production_statement" and
  .sequence == 0 and
  .pool_hex == "94d5641ee2e3891341b7f738f6b36087c184d828ea07463fe5e70d8c332d1051" and
  .nullifier_hex == "aca93a77007946734dc0a906c77dd5323f10c97a13903a7d4615f9227c32dc74" and
  .selection_rule == "least Good23 selector from three post-final branches" and
  .witness_independent_public_metadata == true
' proof/statement.json >/dev/null

jq -e '
  ._publication_provenance.source_artifact_sha256 == "e761782d6067a667bd36fff24322d199400382e2b869aa78a54e92b18ce3f440" and
  .release_certificate_path == "certificates/release-execution-time.json" and
  .network == "devnet" and
  .genesis_hash == "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG" and
  .release_certificate_sha256 == "d83f6df645a00f28090e78f8648974ec94afd35f4677f5d84525ba6af7a2688f" and
  .proof_sha256 == "d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d" and
  .statement_sha256 == "947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2" and
  .sbf_sha256 == "97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a" and
  .release_gate_count == 36 and
  .final_transaction.signature == "4HRnTBPqSh9HW4Nw52rJgnd36fzR6CiKgiaL29WkeH4Gk4xLJVhGEt9CAStyUTpuajo9sw4iDLXQHWwFFQALWmto" and
  .final_transaction.finalized_slot == 476282685 and
  .final_transaction.compute_units_consumed == 1340749 and
  .sequence_before == 0 and
  .sequence_after == 1 and
  .proof_account_absent_after_refund == true and
  .duplicate_simulation_rejected == true and
  .final_transaction_submitted_identically_to_simulation == true
' evidence/devnet-finalized.raw.public.json >/dev/null

jq -e '
  ._publication_provenance.source_artifact_sha256 == "22d4a56fc9e66d3d10313b159eeaa89310077d4b3bdce03c94030e9b31ee17af" and
  .release_certificate_path == "certificates/release-execution-time.json" and
  .artifact == "profile23_mainnet_beta_finalized_demo" and
  .network == "mainnet-beta" and
  .genesis_hash == "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d" and
  .release_certificate_sha256 == "d83f6df645a00f28090e78f8648974ec94afd35f4677f5d84525ba6af7a2688f" and
  .proof_sha256 == "d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d" and
  .statement_sha256 == "947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2" and
  .sbf_sha256 == "97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a" and
  .upgradeable_program_after_finality.programdata_account.data_len == 921893 and
  .upgradeable_program_after_finality.programdata_account.data_sha256 == "7fe4c7352f19ed00a3ba72b3dc6038943db3e5311c23cd5c1b0f8dbb15c4cda2" and
  .upgradeable_program_after_finality.programdata_slot == 432933454 and
  .upgradeable_program_after_finality.upgrade_authority_address == "nKPUvz9bj3XxxpmouXuiXj1DEv33zcVBk41ffJFGqhy" and
  .upgradeable_program_before_setup_exact_release_sbf_max_len_authority == true and
  .upgradeable_program_before_final_simulation_exact_release_sbf_max_len_authority == true and
  .upgradeable_program_after_finality_exact_release_sbf_max_len_authority == true and
  (.upgradeable_program_after_finality_continuity | all(.[]; . == true)) and
  .final_transaction.signature == "4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo" and
  .final_transaction.finalized_slot == 432933949 and
  .final_transaction.compute_units_consumed == 1343749 and
  .final_transaction_finalized_proof_digest_log.logged_proof_sha256 == .proof_sha256 and
  .final_transaction_proof_digest_logs_both_exact == true and
  .sequence_before == 0 and
  .sequence_after == 1 and
  .proof_account_absent_after_refund == true and
  .duplicate_simulation_rejected == true and
  .duplicate_simulation_expected_nullifier_error_exact == true and
  .replay_probe_close_transaction.signature == "5NEPT1TD34p7fN1yKTCEDH1cBwY1HLgJFH4Y1yMD8GkLP9gGYGPjKgQaapsnMwRNpr1BVTopGYsHgEEpKEVwiurN" and
  .replay_probe_close_transaction.finalized_slot == 432934056
' evidence/mainnet-execution.raw.public.json >/dev/null

jq -e '
  .artifact == "profile23_mainnet_finalized_manifest" and
  .generated_at_utc == "2026-07-15T06:47:22Z" and
  .status == "finalized_success_reclaimed_and_refunded" and
  .release.certificate_sha256 == "4ace42c0954bee74382520bbb0818da86e570ec9b212c61cb21130dc644a2725" and
  .release.execution_time_certificate.sha256 == "d83f6df645a00f28090e78f8648974ec94afd35f4677f5d84525ba6af7a2688f" and
  .release.execution_time_certificate.exact_release_used_by_mainnet_preflight == true and
  .release.post_execution_metadata_regeneration.substantive_release_fields_identical == true and
  .source_evidence.repository_readiness.sha256 == "be9d5344a29befaf24af5483a2187250e6793908f832efe957477645469ae480" and
  .source_evidence.repository_readiness.corrected_publication_preflight == true and
  .source_evidence.repository_readiness.readiness_is_execution_attestation == false and
  .source_evidence.execution_time_readiness.sha256 == "463c82a484d27bff3f6d616f94137860339f8be823a74c6f3e22968dc81fe237" and
  .source_evidence.execution_time_readiness.exact_pre_execution_record == true and
  .finalized_transactions.verification.signature == "4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo" and
  .finalized_transactions.verification.slot == 432933949 and
  .finalized_transactions.verification.block_time_unix == 1784065236 and
  .finalized_transactions.verification.compute_units_consumed == 1343749 and
  .finalized_transactions.verification.meta_err == null and
  .finalized_transactions.verification.logged_proof_matches_release == true and
  .finalized_transactions.verification.logged_proof_sha256 == .release.proof.sha256 and
  .finalized_transactions.programdata_cleanup.signature == "3ZsVsjAP4wtA6KM6PygR272Wy1tuxMR9c4Zy4A4YAnTNekuTpQeUCXa8DKnpyEY52bRL8HUjz5AcQpBk4Pw9vwNk" and
  .finalized_transactions.refund_sweep.signature == "2o49MBB2GHRe3ECrDpnrUpmk3DwpfsFHJ7AuTJXp1BcV9EJMGdYFUEeQrxi7yYiehreP8RUa8tiKZQUNAigjwygZ" and
  .cost_reconciliation.initial_payer_balance_lamports == 7000021000 and
  .cost_reconciliation.returned_to_funding_source_lamports == 6985137600 and
  .cost_reconciliation.final_payer_balance_lamports == 0 and
  .cost_reconciliation.total_nonrefundable_cost_lamports == 14883400 and
  .cost_reconciliation.aggregate_payer_transaction_fees_lamports == 11125000 and
  .cost_reconciliation.retained_rent_lamports == 3758400 and
  (.cost_reconciliation.initial_payer_balance_lamports ==
    .cost_reconciliation.returned_to_funding_source_lamports +
    .cost_reconciliation.final_payer_balance_lamports +
    .cost_reconciliation.total_nonrefundable_cost_lamports) and
  (.cost_reconciliation.total_nonrefundable_cost_lamports ==
    .cost_reconciliation.aggregate_payer_transaction_fees_lamports +
    .cost_reconciliation.retained_rent_lamports) and
  .cost_reconciliation.all_equations_reconciled == true and
  .independent_reconciliation.all_predicates_match == true
' evidence/mainnet-finalized-manifest.json >/dev/null

jq -e '
  .artifact == "profile23_mainnet_independent_rpc_reconciliation" and
  .comparison.all_predicates_match == true and
  .cluster_disambiguation.mainnet_beta_result_non_null_on_both_providers == true and
  .cluster_disambiguation.official_devnet_result == null and
  .cluster_disambiguation.official_testnet_result == null and
  (.sanitized_raw_transaction_observations | length) == 6 and
  (.sanitized_raw_final_account_observations as $a |
    $a.addresses_in_order == [
      "6JLAQb2om9yxMru6KW7NeNxhpsoth9Ah3iTQHkTD67oc",
      "9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z",
      "G7XHkv6riJ8TQJ6R8o31wAUMaoL8Q5UyHGExpQ51ntp1",
      "B1z4gQ82xerghDKZ68HuP2Tehx5ER5mfVHq74y4ew3kk",
      "2CnUJycxkinN3XtpWH5bCYVDEuMx42BTnFU9WXsymAu3"
    ] and
    $a.solana_official_mainnet_rpc == $a.publicnode_mainnet_rpc and
    ($a.solana_official_mainnet_rpc | length) == 5 and
    $a.solana_official_mainnet_rpc[0] == null and
    $a.solana_official_mainnet_rpc[1].lamports == 1141440 and
    $a.solana_official_mainnet_rpc[1].owner == "BPFLoaderUpgradeab1e11111111111111111111111" and
    $a.solana_official_mainnet_rpc[1].executable == true and
    $a.solana_official_mainnet_rpc[1].data_base64 == "AgAAAOCLCVp8TcShaA6DWncbHpAsSXx1J8bzZBWLD1Vi9Pqa" and
    $a.solana_official_mainnet_rpc[2] == null and
    $a.solana_official_mainnet_rpc[3].lamports == 1224960 and
    $a.solana_official_mainnet_rpc[3].owner == "9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z" and
    $a.solana_official_mainnet_rpc[3].executable == false and
    $a.solana_official_mainnet_rpc[3].data_base64 == "QVNQUwEAAAABAAAAAAAAAMTrDFOnmkogX7J9SKRKPF0kZzNc+8pja5dG7wi0Rtgr" and
    $a.solana_official_mainnet_rpc[4].lamports == 1392000 and
    $a.solana_official_mainnet_rpc[4].owner == "9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z" and
    $a.solana_official_mainnet_rpc[4].executable == false and
    $a.solana_official_mainnet_rpc[4].data_base64 == "QVNQTgEAAACU1WQe4uOJE0G39zj2s2CHwYTYKOoHRj/l5w2MMy0QUaypOncAeUZzTcCpBsd91TI/EMl6E5A6fUYV+SJ8Mtx0") and
  ([.sanitized_raw_transaction_observations[] |
    .requested_signature == .solana_official_mainnet_rpc.first_signature and
    .requested_signature == .publicnode_mainnet_rpc.first_signature and
    .solana_official_mainnet_rpc.slot == .publicnode_mainnet_rpc.slot and
    .solana_official_mainnet_rpc.blockTime == .publicnode_mainnet_rpc.blockTime and
    .solana_official_mainnet_rpc.meta == .publicnode_mainnet_rpc.meta] | all) and
  ([.sanitized_raw_transaction_observations[] | select(.purpose == "tag65_atomic_verify_and_apply")][0] as $v |
    $v.solana_official_mainnet_rpc.blockTime == 1784065236 and
    $v.solana_official_mainnet_rpc.slot == 432933949 and
    $v.solana_official_mainnet_rpc.meta.err == null and
    $v.publicnode_mainnet_rpc.meta.err == null and
    $v.solana_official_mainnet_rpc.meta.computeUnitsConsumed == 1343749 and
    $v.solana_official_mainnet_rpc.program_log == $v.publicnode_mainnet_rpc.program_log and
    $v.solana_official_mainnet_rpc.program_success_log == "Program 9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z success" and
    $v.publicnode_mainnet_rpc.program_success_log == "Program 9kPpUknrRicMvaGa6zPNERGUYDj6fMvMR8PwMS3iFR6Z success" and
    $v.decoded_program_log.domain == "aspis-proof-sha256-v1" and
    $v.decoded_program_log.proof_sha256 == "d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d" and
    ($v.solana_official_mainnet_rpc.meta.postBalances[0] +
      $v.solana_official_mainnet_rpc.meta.fee +
      $v.solana_official_mainnet_rpc.meta.postBalances[2] ==
      $v.solana_official_mainnet_rpc.meta.preBalances[0] +
      $v.solana_official_mainnet_rpc.meta.preBalances[1]))
' evidence/mainnet-independent-rpc-reconciliation.json >/dev/null

jq -e '
  ._publication_provenance.source_artifact_sha256 == "559a7be08bb109ba9b307e843e33ca92324f1e752ada75622b722ea91f5c6b7e" and
  .artifact == "profile23_programdata_cleanup_preclose" and
  .expected_signature == "3ZsVsjAP4wtA6KM6PygR272Wy1tuxMR9c4Zy4A4YAnTNekuTpQeUCXa8DKnpyEY52bRL8HUjz5AcQpBk4Pw9vwNk" and
  .programdata_lamports == 6417266160 and
  .simulation.err == null and
  .simulation.exact_signed_wire_simulated == true and
  .submission_performed_when_written == false and
  (has("signed_wire_base64") | not)
' evidence/mainnet-cleanup-preclose.raw.public.json >/dev/null

jq -e '
  ._publication_provenance.source_artifact_sha256 == "25a921ac906996a8114bf54ca421d20dd04a4cf8b3aa73306d38a28e4a1f0bdc" and
  .artifact == "profile23_programdata_cleanup_postclose" and
  .signature == "3ZsVsjAP4wtA6KM6PygR272Wy1tuxMR9c4Zy4A4YAnTNekuTpQeUCXa8DKnpyEY52bRL8HUjz5AcQpBk4Pw9vwNk" and
  .finalized_slot == 432934227 and
  .preclose_evidence_sha256 == "559a7be08bb109ba9b307e843e33ca92324f1e752ada75622b722ea91f5c6b7e" and
  .programdata_account_absent == true and
  .refund.refund_lamports == 6417266160 and
  .refund.exact_refund_equation_reconciled == true
' evidence/mainnet-cleanup.raw.public.json >/dev/null

jq -e '
  .artifact == "profile23_mainnet_refund_sweep_finalized_receipt_v1" and
  .signature == "2o49MBB2GHRe3ECrDpnrUpmk3DwpfsFHJ7AuTJXp1BcV9EJMGdYFUEeQrxi7yYiehreP8RUa8tiKZQUNAigjwygZ" and
  .finalized_slot == 432934316 and
  .transfer_lamports == 6985137600 and
  .fee_lamports == 5000 and
  .payer_post_lamports == 0 and
  .payer_pre_equals_transfer_plus_fee == true and
  .destination_delta_equals_transfer == true and
  (.independent_finalized_reconciliation | all(.[]; . == true))
' evidence/mainnet-sweep.raw.json >/dev/null

jq -n -e \
  --slurpfile m manifest.json \
  --slurpfile r certificates/release.json \
  --slurpfile x certificates/release-execution-time.json \
  --slurpfile q certificates/mainnet-readiness.json \
  --slurpfile h certificates/mainnet-readiness-execution-time.json \
  --slurpfile d evidence/devnet-finalized.raw.public.json \
  --slurpfile e evidence/mainnet-execution.raw.public.json \
  --slurpfile f evidence/mainnet-finalized-manifest.json \
  --slurpfile i evidence/mainnet-independent-rpc-reconciliation.json \
  --slurpfile p evidence/mainnet-cleanup-preclose.raw.public.json \
  --slurpfile c evidence/mainnet-cleanup.raw.public.json \
  --slurpfile w evidence/mainnet-sweep.raw.json \
  --slurpfile s proof/statement.json '
    ($m[0]) as $m | ($r[0]) as $r | ($x[0]) as $x | ($q[0]) as $q |
    ($h[0]) as $h | ($d[0]) as $d | ($e[0]) as $e |
    ($f[0]) as $f | ($i[0]) as $i | ($p[0]) as $p | ($c[0]) as $c |
    ($w[0]) as $w | ($s[0]) as $s |
    $m.release_instance.proof_sha256 == $r.proof.sha256 and
    $m.release_instance.proof_sha256 == $x.proof.sha256 and
    $m.release_instance.proof_sha256 == $d.proof_sha256 and
    $m.release_instance.proof_sha256 == $e.proof_sha256 and
    $m.release_instance.proof_sha256 == $f.release.proof.sha256 and
    $m.release_instance.statement_sha256 == $r.release_instance.statement_sha256 and
    $m.release_instance.statement_sha256 == $x.release_instance.statement_sha256 and
    $m.release_instance.statement_sha256 == $e.statement_sha256 and
    $m.release_instance.sbf_sha256 == $r.default_production_sbf.sha256 and
    $m.release_instance.sbf_sha256 == $x.default_production_sbf.sha256 and
    $m.release_instance.sbf_sha256 == $e.sbf_sha256 and
    $r.release_instance.statement_pool_hex == $s.pool_hex and
    $m.mainnet.verification_signature == $e.final_transaction.signature and
    $m.mainnet.verification_signature == $f.finalized_transactions.verification.signature and
    $m.mainnet.verification_finalized_slot == $e.final_transaction.finalized_slot and
    $m.mainnet.verification_compute_units == $e.final_transaction.compute_units_consumed and
    $m.mainnet.programdata_close_signature == $p.expected_signature and
    $m.mainnet.programdata_close_signature == $c.signature and
    $m.mainnet.sweep_signature == $w.signature and
    $m.mainnet.returned_lamports == $w.transfer_lamports and
    $m.mainnet.final_payer_lamports == $w.payer_post_lamports and
    $m.mainnet.nonrefundable_lamports == $f.cost_reconciliation.total_nonrefundable_cost_lamports and
    $q.readiness_is_execution_attestation == false and
    $q.release_certificate_sha256 == $h.release_certificate_sha256 and
    $h.release_certificate_sha256 == $e.release_certificate_sha256 and
    $f.release.certificate_sha256 == $m.certificate_lineage.publication_certificate_sha256 and
    $f.release.execution_time_certificate.sha256 == $m.certificate_lineage.execution_time_certificate_sha256 and
    $i.comparison.all_predicates_match == true
  ' >/dev/null

if grep -RIlE '/Users/|"signed_wire_base64"|BEGIN (RSA |OPENSSH |EC )?PRIVATE KEY' \
  --include='*.json' --include='*.md' --include='*.html' . >/dev/null; then
  fail "public text contains a prohibited operator path, serialized wire payload, or private key marker"
fi

if find . -type f \( -iname '*keypair*' -o -iname '*funding-manifest*' -o -iname '*recovery.jsonl*' \) |
  grep -q .; then
  fail "bundle contains a prohibited operational file"
fi

if grep -RhoE 'https://(explorer\.solana\.com|solscan\.io)/tx/[^" )]+' \
  --include='*.json' --include='*.md' --include='*.html' . | grep -Fv '?cluster=' >/dev/null; then
  fail "bundle contains an explorer transaction link without an explicit cluster"
fi

printf 'Profile23 q18/g37 mainnet-v1 bundle verified.\n'
