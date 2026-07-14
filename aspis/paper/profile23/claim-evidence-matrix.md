# Profile 23 claim-to-evidence matrix

Status: manuscript draft. This matrix is not itself evidence and must not
be cited as a proof. The canonical numeric source is
`results/stage2/profile23_one_transaction_release.json`; generated paper
macros must read that file and reject any cross-artifact mismatch.

Current status (`2026-07-14`): the q18/cap17 local release is green at 35/35
gates and binds the mined proof, production KATs, theorem artifacts, and
release certificate. The `2026-07-13` q16/cap16 certificate is explicitly
superseded; its proof, SBF, and CU measurements are historical evidence only.

Status vocabulary:

- `artifact-green`: the pinned local artifact reports the condition green;
- `proof-required`: the manuscript still needs a complete theorem and review;
- `experiment-required`: the paper artifact still needs the named run/data;
- `local-release-green`: the pinned q18 local release certificate reports all
  required gates green; this is not deployment, audit, or mainnet evidence;
- `devnet-evidence-green`: the exact released proof/program transaction and
  post-state are bound by the immutable finalized devnet evidence object; and
- `blocked`: public claim prohibited until the stated external gate closes.

<!-- markdownlint-disable MD013 -->

| ID | manuscript claim | exact scope and qualifiers | theorem or evidence | canonical source | status / blocking condition |
| --- | --- | --- | --- | --- | --- |
| C01 | Profile 23 proves a shielded spend relation | Atomic-v3, one input, one output, depth-20 same-private-path replacement only | `def:profile23-relation`; executable semantic oracle and trace correspondence | `crates/aspis-statement/src/spend.rs`; `crates/aspis-statement/src/atomic_statement.rs` | proof-required |
| C02 | transparent setup | No structured reference string, secret trapdoor, or trusted setup; ROM and stated hash/code assumptions remain | `def:profile23-transparent-parameters`; assumption table | frozen source, generated constants, imported theorem pins | proof-required |
| C03 | over-100-bit proven-Johnson/MCA soundness | Active q18 classical ROM argument soundness for `R23`; work-normalized BCS endpoints and factor-40 sensitivity included; not knowledge soundness or a standard-model theorem | `lem:circle-grs-transport` through `thm:bcs-soundness` | `profile23_d_after_g_soundness_epro.json`; released certificate JSON | local-release-green; proof-required |
| C04 | no capacity-conjecture reliance | Exact rate-1/512/q18 instantiation stays in the stated Johnson/MCA regime | imported-theorem hypothesis table and local transport/fold proofs | soundness ledger plus pinned theorem versions | proof-required |
| C05 | real-view versus simulator hiding | Complete declared verifier view, classical SHA-256 programmable ROM, `Q_H <= 2^128`, `A <= 17`, fixed Proof-or-Abort channel | `alg:sim23`; `thm:real-vs-sim23` | hiding-closure JSON; released certificate JSON | local-release-green; proof-required |
| C06 | two-witness pairwise hiding | Fixed `x`; any valid `w0,w1 in R23(x)`; auxiliary input and post-output queries; triangle-inequality loss retained | `cor:pairwise-hiding` | hiding-closure JSON; released certificate JSON | local-release-green; proof-required |
| C07 | complete declared view | Proof account, proof length, roots/openings/frontiers, transcript/work, selector/Abort, framing/logs, deterministic mutation; excludes network/account-graph/local/physical observables | `def:profile23-complete-view` | hiding-closure view inventory | proof-required |
| C08 | q3 selector is soundness-safe | Commitments fixed before domain-separated q3 schedules; least Good selected; factor three applies only as justified in ledger | `lem:selector-soundness` | soundness/EPRO ledger and transcript KAT | proof-required |
| C09 | selector and Abort do not leak the witness | Joint schedule/Good/least-selector/all-bad law is witness-independent; privacy theorem includes Abort | `lem:selection-hiding-abort` | hiding-closure q3/cap17 artifact | proof-required |
| C10 | Good23 gives exact affine simulation | Image equality, dimensions/rank/kernel cardinality, constant-size mask preimages, uniform induced image distribution | `lem:good23-product`; `lem:complete-affine-image`; `lem:uniform-mask-preimages` | Good23 product and rank-transfer artifacts | proof-required; independent checker required |
| C11 | EPRO/private-Merkle/work simulation | Explicit adjacent hybrids, distinct-input inventory, prequeries, collisions, adaptive later queries, canonical work, serialization/finalization/mutation | `lem:epro-complete-view` | hiding-closure and soundness/EPRO artifacts | proof-required |
| C12 | canonical proof identity and size | The released canonical q18 mined proof is 66,367 bytes; schedule-dependent length is public | generated artifact table | release JSON `proof` object and proof bytes | local-release-green; devnet-evidence-green; q16 identity is historical only |
| C13 | default SBF identity and size | Released 915,656-byte q18 manifest-default build, byte-bound to the devnet ProgramData snapshot | generated artifact table, release rebuild, devnet continuity checks | release JSON `default_production_sbf` object; finalized devnet evidence | local-release-green; devnet-evidence-green |
| C14 | verifier fits the CU cap | Worst literal local tag-60 path is 1,314,386 CU; the finalized devnet transaction used 1,314,332 CU under the 1.4M limit | integrated CU reconciliation and finalized transaction replay | release JSON CU/headroom fields; finalized devnet evidence | local-release-green; devnet-evidence-green |
| C15 | one transaction | Exactly verification plus nullifier/pool mutation consuming a finalized, pre-uploaded proof account | transaction-scope definition and raw transaction | release JSON `scope` object | local-release-green; title/abstract qualifier mandatory |
| C16 | finalized proof account is required | Zero-sentinel and ownership checks in the frozen program; no intrinsic chain-level immutability claim | `lem:finalized-account-state-machine`; mutation/finalization matrix | source, release gates, Tier-1/Tier-3 tests | proof-required |
| C17 | atomic nullifier and pool transition | Verify-before-write order, precondition recheck, exact post-images, rollback and lock assumptions | `prop:atomic-refinement`; raw validator account images | q18 production mutation KAT and adversarial tests | local-release-green; proposition/replay required |
| C18 | configured program address | The address is the frozen configuration and the observed devnet deployment; it is not a mainnet address | generated artifact table and Program/ProgramData snapshots | source/build configuration; finalized devnet evidence | devnet-evidence-green |
| C19 | deployed/mainnet result | Successful finalized transaction bound to exact ProgramData/SBF/proof/accounts/CU | immutable mainnet evidence object | none yet | blocked |
| C20 | historical priority or “first” | Exact qualified claim only after mainnet gate and publication-day rescan | dated novelty method and evidence | novelty artifact plus future mainnet evidence | blocked |
| C21 | audited or production-ready | Requires independent audit and operational readiness evidence beyond tests | external reports | none | blocked |
| C22 | setup lifecycle cost | Fresh release instance uses 109 setup transactions including 104 uploads; evidence records signatures, slots, CU and rent allocation | lifecycle experiment table | finalized devnet evidence | devnet-evidence-green; wall-clock distribution remains future work |
| C23 | prover/miner cost | Wall time, memory, q3 attempts, Abort rate, PoW mining, complete time-to-spend | prover/miner experiment table | new raw Tier-5 artifacts | experiment-required |
| C24 | throughput and contention | Same/different nullifier and pool workloads; writable locks, per-slot throughput and DoS limitations | contention experiment table | new raw validator artifacts | experiment-required |
| C25 | program immutability | Requires Program/ProgramData linkage, byte identity, capacity, finalized slot, and no upgrade authority | finalized-account theorem assumption plus deployment evidence | none for a deployment | blocked; local paper must state upgrade assumption |
| C26 | finalized devnet rehearsal | Exact release proof/SBF, 109 setup transactions, byte-identical signed simulation/submission, slot 476231605, sequence 0-to-1, nullifier creation, post-state and negative replay checks | evaluation section and raw transaction | mode-0444 devnet evidence SHA-256 `360e38fc5db3b644586c29e7a872203e8f9507c9ddef52add776fefb5d300275` | devnet-evidence-green; not mainnet or audit evidence |

<!-- markdownlint-enable MD013 -->

## Authoring rule

Every abstract sentence, contribution bullet, theorem conclusion, table
caption, and quantitative evaluation sentence must cite at least one matrix
ID in source comments. Before submission, a generated audit checks that every
used ID exists, that no `blocked` ID appears as an affirmative claim, and that
numeric claims are macros derived from the canonical release manifest rather
than copied from this scaffold.
