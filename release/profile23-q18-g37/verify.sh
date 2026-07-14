#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

fail() {
  printf 'FAIL: %s\n' "$*" >&2
  exit 1
}

command -v jq >/dev/null 2>&1 || fail "jq is required"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c SHA256SUMS
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c SHA256SUMS
else
  fail "sha256sum or shasum is required"
fi

check_size() {
  local expected=$1
  local file=$2
  local actual
  actual=$(wc -c < "$file" | tr -d '[:space:]')
  [[ "$actual" == "$expected" ]] || fail "$file has $actual bytes; expected $expected"
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

check_object() {
  local expected_size=$1
  local expected_sha256=$2
  local file=$3
  local actual_sha256
  check_size "$expected_size" "$file"
  actual_sha256=$(sha256_file "$file")
  [[ "$actual_sha256" == "$expected_sha256" ]] || fail "$file has unexpected SHA-256"
}

check_object 2281 b45239f4fcec167c121852fdd67813d4a599847f039e3a77ab146eb9c12a4fb1 manifest.json
check_object 20073 b02eae619f685449a84095243f5d07be78f91ca7df67b435fb2c12aef8f39fcf certificates/release.json
check_object 7216 ddbe026884875f62b215277ec2028b4531bb6933a969c46dbd540a57a538f8aa certificates/preflight-readiness.json
check_object 61342 360e38fc5db3b644586c29e7a872203e8f9507c9ddef52add776fefb5d300275 evidence/devnet-finalized.raw.json
check_object 588517 c42433cfbfe7cca618a0d240187665ac610cb78f5dcb172e5e5f2634e1fd1abf paper/profile23.pdf
check_object 915656 da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254 program/aspis_verifier.so
check_object 66367 f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53 proof/profile23-q18-g37.bin
check_object 667 976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de proof/statement.json

proof_header=$(od -An -tx1 -N16 proof/profile23-q18-g37.bin | tr -d '[:space:]')
[[ "$proof_header" == "4153503004170a09120020000204020b" ]] || fail "unexpected proof header"

jq -e '
  .artifact == "aspis_profile23_q18_g37_publication_bundle" and
  .version == 1 and
  .release_id == "profile23-q18-g37" and
  .profile.queries == 18 and
  .profile.batch_grinding_bits == 37 and
  .profile.release_gates_passed == 35 and
  .profile.release_gates_total == 35 and
  .profile.conservative_soundness_floor_bits == 100.16144938287457 and
  .profile.pairwise_witness_hiding_bits == 103.02492234825198 and
  .profile.real_vs_simulator_hiding_bits == 104.02492234825198 and
  .parameters.fold_grinding_bits == [34, 33, 30, 25] and
  .parameters.final_grinding_bits == 32 and
  .source.commit == "020f8f87238435dc2e1dc8cb41df90670fcb94f6" and
  .devnet.program_id == "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue" and
  .devnet.programdata_address == "cdRqe7MGCEJ2Z6iZfWuXtuymRiAhXtyfDgT47sKZr69" and
  .devnet.upgrade_authority == "8AFmGcC2azHYGJz1VrDb8qJbCYdhVBTM5GE6TTSY3W2k" and
  .devnet.signature == "3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx" and
  .devnet.finalized_slot == 476231605 and
  .devnet.compute_units == 1314332 and
  .objects["certificates/release.json"] == {"bytes":20073,"sha256":"b02eae619f685449a84095243f5d07be78f91ca7df67b435fb2c12aef8f39fcf"} and
  .objects["certificates/preflight-readiness.json"] == {"bytes":7216,"sha256":"ddbe026884875f62b215277ec2028b4531bb6933a969c46dbd540a57a538f8aa"} and
  .objects["evidence/devnet-finalized.raw.json"] == {"bytes":61342,"sha256":"360e38fc5db3b644586c29e7a872203e8f9507c9ddef52add776fefb5d300275"} and
  .objects["paper/profile23.pdf"] == {"bytes":588517,"sha256":"c42433cfbfe7cca618a0d240187665ac610cb78f5dcb172e5e5f2634e1fd1abf"} and
  .objects["program/aspis_verifier.so"] == {"bytes":915656,"sha256":"da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254"} and
  .objects["proof/profile23-q18-g37.bin"] == {"bytes":66367,"sha256":"f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53"} and
  .objects["proof/statement.json"] == {"bytes":667,"sha256":"976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de"}
' manifest.json >/dev/null

jq -e '
  .artifact == "profile23_one_transaction_release" and
  .released == true and
  .status == "released_all_required_gates_green" and
  (.gates | length) == 35 and
  (.gates | all(.passed == true)) and
  (.failed_gates | length) == 0 and
  .coarse_whole_soundness_floor_bits == 100.16144938287457 and
  .computational_hiding_pairwise_witness_bound_bits == 103.02492234825198 and
  .computational_hiding_real_vs_simulator_bound_bits == 104.02492234825198 and
  .max_literal_production_tag60_cu == 1314386 and
  .exact_headroom_under_1_4m_cu == 85614 and
  .proof.bytes == 66367 and
  .proof.sha256 == "f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53" and
  .release_instance.statement_bytes == 667 and
  .release_instance.statement_sha256 == "976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de" and
  .release_instance.statement_sequence == 0 and
  .release_instance.serialized_selector == 0 and
  .release_instance.least_good_selector == 0 and
  .release_instance.selector_candidates == 3 and
  (.release_instance.good23_branches | length) == 3 and
  (.release_instance.good23_branches | all(.accepted == true)) and
  .release_instance.production_host_verification_green == true and
  .release_instance.evaluation_error == null and
  .default_production_sbf.bytes == 915656 and
  .default_production_sbf.sha256 == "da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254"
' certificates/release.json >/dev/null

jq -e '
  .artifact == "profile23_production_statement" and
  .sequence == 0 and
  .pool_hex == "504c9d4be70ef96a37d9aff3d9fd1b5080726efd6596c54a12817fd2e2d9c67a" and
  .selection_rule == "least Good23 selector from three post-final branches" and
  .witness_independent_public_metadata == true
' proof/statement.json >/dev/null

jq -e '
  .artifact == "profile23_devnet_readiness" and
  .mode == "read_only" and
  .mutations_performed == false and
  .ready == true and
  (.gates | length) == 27 and
  (.gates | all(.passed == true)) and
  (.blockers | length) == 0 and
  .release_sha256 == "b02eae619f685449a84095243f5d07be78f91ca7df67b435fb2c12aef8f39fcf" and
  .proof_sha256 == "f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53" and
  .statement_sha256 == "976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de" and
  .sbf_sha256 == "da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254"
' certificates/preflight-readiness.json >/dev/null

jq -e '
  .network == "devnet" and
  .genesis_hash == "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG" and
  .program_id == "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue" and
  .release_certificate_sha256 == "b02eae619f685449a84095243f5d07be78f91ca7df67b435fb2c12aef8f39fcf" and
  .proof_sha256 == "f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53" and
  .statement_sha256 == "976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de" and
  .sbf_sha256 == "da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254" and
  .release_gate_count == 35 and
  (.setup_transactions | length) == 109 and
  ([.setup_transactions[].signature] | unique | length) == 109 and
  ([.setup_transactions[] | select(.label | startswith("upload_proof_chunk_"))] | length) == 104 and
  ([.setup_transactions[] | select(.label | startswith("upload_proof_chunk_"))] |
    to_entries | all(.value.label == ("upload_proof_chunk_" + (.key | tostring)))) and
  .proof_bytes == 66367 and
  .sbf_bytes == 915656 and
  .proof_account_finalized == true and
  .post_finalize_upload_rejected == true and
  .post_finalize_second_finalize_rejected == true and
  .duplicate_simulation_rejected == true and
  .production_host_verification_green == true and
  .release_instance_declared_host_verification_green == true and
  .release_instance_good23_fingerprint_exact == true and
  .release_instance_proof_identity_exact == true and
  .release_instance_selector_binding_exact == true and
  .release_instance_statement_identity_exact == true and
  .final_transaction_submitted_identically_to_simulation == true and
  .final_transaction.signature == "3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx" and
  .final_transaction.finalized_slot == 476231605 and
  .final_transaction.compute_units_consumed == 1314332 and
  .final_transaction_simulation_cu == 1314332 and
  .sequence_before == 0 and
  .sequence_after == 1 and
  .nullifier_before == null and
  .nullifier_after.address == "AbWC9vKT7mxRNLeCnFrfi9HFsncF73XfG9TnbJS2jXHy" and
  .pool_before.address == .pool_after.address and
  .pool_before.data_sha256 != .pool_after.data_sha256 and
  .final_transaction.message_sha256 == .final_transaction_message_sha256 and
  .final_transaction.serialized_transaction_sha256 == .final_transaction_wire_sha256 and
  .upgradeable_program_before_final_simulation_exact_release_sbf_max_len_authority == true and
  .upgradeable_program_after_finality_exact_release_sbf_max_len_authority == true and
  (.upgradeable_program_before_final_simulation_continuity | all(.[]; . == true)) and
  (.upgradeable_program_after_finality_continuity | all(.[]; . == true))
' evidence/devnet-finalized.raw.json >/dev/null

jq -n -e \
  --slurpfile m manifest.json \
  --slurpfile r certificates/release.json \
  --slurpfile p certificates/preflight-readiness.json \
  --slurpfile e evidence/devnet-finalized.raw.json \
  --slurpfile s proof/statement.json '
    ($m[0]) as $m | ($r[0]) as $r | ($p[0]) as $p | ($e[0]) as $e | ($s[0]) as $s |
    $m.devnet.program_id == $e.program_id and
    $m.devnet.programdata_address == $e.upgradeable_program_after_finality.programdata_address and
    $m.devnet.upgrade_authority == $e.upgradeable_program_after_finality.upgrade_authority_address and
    $m.devnet.signature == $e.final_transaction.signature and
    $m.devnet.finalized_slot == $e.final_transaction.finalized_slot and
    $m.devnet.compute_units == $e.final_transaction.compute_units_consumed and
    $r.release_instance.proof_sha256 == $p.proof_sha256 and
    $r.release_instance.proof_sha256 == $e.proof_sha256 and
    $r.release_instance.statement_sha256 == $p.statement_sha256 and
    $r.release_instance.statement_sha256 == $e.statement_sha256 and
    $r.default_production_sbf.sha256 == $p.sbf_sha256 and
    $r.default_production_sbf.sha256 == $e.sbf_sha256 and
    $p.release_sha256 == $e.release_certificate_sha256 and
    $r.release_instance.canonical_public_input_digest == $e.canonical_public_input_digest and
    $r.release_instance.serialized_selector == $e.serialized_selector and
    $r.release_instance.least_good_selector == $e.least_good_selector and
    $r.release_instance.good23_definition_fingerprint == $e.good23_definition_fingerprint and
    $r.release_instance.statement_pool_hex == $s.pool_hex and
    $r.release_instance.statement_sequence == $s.sequence and
    $p.program_id == $e.program_id and
    $p.pool_pubkey == $e.pool_before.address and
    $p.pool_pubkey == $e.pool_after.address and
    $p.proof_account_pubkey == $e.proof_account.address and
    $p.nullifier_address == $e.nullifier_after.address and
    $e.final_transaction.compute_units_consumed <= $r.max_literal_production_tag60_cu
  ' >/dev/null

printf 'Profile23 q18/g37 bundle verified.\n'
