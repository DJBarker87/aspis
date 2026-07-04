{
  "review": {
    "security_score": "B-",
    "quality_score": "B",
    "ready_for_mainnet": false,
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
      }
    ]
  }
}
