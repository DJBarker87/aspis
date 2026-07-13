{
  "review": {
    "security_score": "C",
    "quality_score": "C+",
    "ready_for_mainnet": false,
    "reviewed_at": "2026-07-10",
    "reviewed_commit": "0f15ba0",
    "review_artifact": "aspis/docs/recent-work-review-2026-07-10.html",
    "verification": {
      "cargo_test_workspace_all_targets": "passed",
      "cargo_clippy_workspace_all_targets_deny_warnings": "failed_with_16_lints",
      "theta_rederivation": "factor_of_rho_correction_reproduced_but_finite_length_constants_not_closed"
    },
    "remediation_2026_07_10": {
      "ready_for_mainnet": false,
      "logup_lambda0_collision": "fixed: tag is lambda^0, limbs are lambda^1..lambda^w; weakened-build teeth, 512-delta property test, and host/SBF compression KAT pass",
      "theta_ledger": "deterministic runner committed; Table-4 3/2 coefficient restored; 93.7263 remains an unquotable sensitivity because finite-n o(n), c1/c2, and circle-code transport are not pinned; 65.5 is the only quotable floor",
      "s2_measurement": "contamination-free isolated A/B is +49,099 CU (86,815 -> 135,914); q36 registered projection is 1,096,660 and strict-red; held q34/g36 recovery projects 1,052,181",
      "wire_compatibility": "restored true first-introduction Borsh tags and pinned all variants 0..18 in a regression test",
      "poseidon2": "hash_fields now uses the differential-tested lazy kernel; current production Verify executes no Poseidon2, so present verifier-gate impact is zero",
      "latest_verification": {
        "cargo_test_workspace_all_targets_all_features": "passed",
        "cargo_clippy_workspace_all_targets_all_features_deny_warnings": "passed",
        "cargo_fmt_check": "passed",
        "retired_number_lint": "14 files; 38 explicitly historical occurrences; 0 violations",
        "logup_host_sbf_kat": "passed; weakened dependency feature mechanically absent",
        "s2_host_sbf_probe": "passed; 5/5 deterministic per arm"
      },
      "next_gate": "integrated v4 statement proof and final-shape multi-draw SBF measurement under the independent t=90 ruling"
    },
    "findings": [
      {
        "severity": "High",
        "category": "Measurement gate",
        "description": "Aspis Stage 0 conditionally closes for Stage 1 on lr10/k64/q32/g32. Johnson q80 and the old lr14 narrow-layout target are measured RED results.",
        "fix": "Stage 1 must justify or kill q32/g32 in the soundness note. If it cannot, q36 is reserve and q40 is too tight for the single-transaction statement plan."
      },
      {
        "severity": "High",
        "category": "Security",
        "description": "The staged upload program lacked persistent upload authority checks before this audit pass.",
        "fix": "Fixed by adding proof-account magic, proof length, upload authority, signer checks for initialization/upload, and short-account rejection in `programs/aspis-verifier/src/lib.rs`."
      },
      {
        "severity": "Medium",
        "category": "Testing",
        "description": "The host JSON corruption artifact omitted replay cases claimed by the gate note.",
        "fix": "Fixed by adding `mode_flag_replay` and `profile_swap` to `xtask/src/host.rs` corruption artifact generation."
      },
      {
        "severity": "Medium",
        "category": "Cryptographic soundness",
        "description": "Stage 1 soundness hardening is intentionally unimplemented, so no public soundness figure is defensible yet.",
        "fix": "Complete `docs/aspis-soundness-note.md`, implement missing PCS checks, and add false-statement adversarial vectors before Stage 2."
      },
      {
        "severity": "Critical",
        "category": "Cryptographic soundness",
        "description": "Tagged LogUp compression uses tag + d0 + lambda*d1 + ..., so distinct tuples (tag,d0,...) and (tag+delta,d0-delta,...) collide for every challenge.",
        "fix": "Start witness limbs at lambda^1, add a coupled tag/value collision vector, and update the T6 argument before integrating the payment statement."
      },
      {
        "severity": "High",
        "category": "Soundness accounting",
        "description": "The revised-conjecture mapping drops Conjecture 2's unbounded o(n) term and calls the Table 4 fold coefficient <=1 even though it is 3/2 at k=0.",
        "fix": "Ratify a named finite-length strengthening with explicit constants and per-round mapping, then regenerate the theta ledger from a checked-in optimizer."
      },
      {
        "severity": "High",
        "category": "Measurement gate",
        "description": "The q43 option omits the registered 17,663-CU composition-stress delta; registered-conservative is 1,197,885 CU while the anchor-corrected sensitivity clears by roughly 30K, leaving two conflicting live gate statistics.",
        "fix": "Name registered-conservative as binding, demote anchor-corrected to sensitivity-only, and record option 3 as gate-marginal but dead by ruling regardless."
      },
      {
        "severity": "High",
        "category": "Evidence integrity",
        "description": "The canonical soundness note and feasibility_decision.json contain contradictory current states from the q45/k83 and q43/k51 eras.",
        "fix": "Make the r=2/k'=51 arithmetic close the sole current block, retain the product gate as open pending integrated v4, and move superseded states under historical keys."
      },
      {
        "severity": "Medium",
        "category": "Wire compatibility",
        "description": "New Borsh instruction variants were inserted before existing variants, changing ordinal wire tags for older clients and transactions.",
        "fix": "Adopt explicit versioned wire tags or restore append-only enum ordering."
      },
      {
        "severity": "Opportunity",
        "category": "Compute optimization",
        "description": "Spend hashing still bypasses the byte-identical optimized Poseidon2 permutation; the checked-in diagnostic SBF probe measures 66,830 CU savings over 49 permutations, but production Verify runs no Poseidon2.",
        "fix": "Route hash_fields through the optimized permutation with differential KAT coverage, while recording zero impact on the current verifier gate unless a future direct-evaluator/deposit instruction integrates and measures this path."
      }
    ]
  }
}
