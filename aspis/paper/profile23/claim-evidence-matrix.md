# Profile 23 claim-to-evidence matrix

Status: manuscript scaffold. This matrix is not itself evidence and must not
be cited as a proof. The canonical numeric source is
`results/stage2/profile23_one_transaction_release.json`; generated paper
macros must read that file and reject any cross-artifact mismatch.

Status vocabulary:

- `artifact-green`: the pinned local artifact reports the condition green;
- `proof-required`: the manuscript still needs a complete theorem and review;
- `experiment-required`: the paper artifact still needs the named run/data;
- `blocked`: public claim prohibited until the stated external gate closes.

<!-- markdownlint-disable MD013 -->

| ID | manuscript claim | exact scope and qualifiers | theorem or evidence | canonical source | status / blocking condition |
| --- | --- | --- | --- | --- | --- |
| C01 | Profile 23 proves a shielded spend relation | Atomic-v3, one input, one output, depth-20 same-private-path replacement only | `def:profile23-relation`; executable semantic oracle and trace correspondence | `crates/aspis-statement/src/spend.rs`; `crates/aspis-statement/src/atomic_statement.rs` | proof-required |
| C02 | transparent setup | No structured reference string, secret trapdoor, or trusted setup; ROM and stated hash/code assumptions remain | `def:profile23-transparent-parameters`; assumption table | frozen source, generated constants, imported theorem pins | proof-required |
| C03 | over-100-bit proven-Johnson/MCA soundness | Classical ROM argument soundness for `R23`; not knowledge soundness or a standard-model theorem | `lem:circle-grs-transport` through `thm:bcs-soundness` | release JSON soundness fields and `profile23_d_after_g_soundness_epro.json` | artifact-green; proof-required |
| C04 | no capacity-conjecture reliance | Exact rate-1/512/q16 instantiation stays in the stated Johnson/MCA regime | imported-theorem hypothesis table and local transport/fold proofs | soundness ledger plus pinned theorem versions | proof-required |
| C05 | real-view versus simulator hiding | Complete declared verifier view, classical SHA-256 programmable ROM, `Q_H <= 2^128`, `A <= 16`, fixed Proof-or-Abort channel | `alg:sim23`; `thm:real-vs-sim23` | release JSON real/simulator field and hiding-closure JSON | artifact-green; proof-required |
| C06 | two-witness pairwise hiding | Fixed `x`; any valid `w0,w1 in R23(x)`; auxiliary input and post-output queries; triangle-inequality loss retained | `cor:pairwise-hiding` | release JSON pairwise field and hiding-closure JSON | artifact-green; proof-required |
| C07 | complete declared view | Proof account, proof length, roots/openings/frontiers, transcript/work, selector/Abort, framing/logs, deterministic mutation; excludes network/account-graph/local/physical observables | `def:profile23-complete-view` | hiding-closure view inventory | proof-required |
| C08 | q3 selector is soundness-safe | Commitments fixed before domain-separated q3 schedules; least Good selected; factor three applies only as justified in ledger | `lem:selector-soundness` | soundness/EPRO ledger and transcript KAT | proof-required |
| C09 | selector and Abort do not leak the witness | Joint schedule/Good/least-selector/all-bad law is witness-independent; privacy theorem includes Abort | `lem:selection-hiding-abort` | hiding-closure q3/cap16 artifact | proof-required |
| C10 | Good23 gives exact affine simulation | Image equality, dimensions/rank/kernel cardinality, constant-size mask preimages, uniform induced image distribution | `lem:good23-product`; `lem:complete-affine-image`; `lem:uniform-mask-preimages` | Good23 product and rank-transfer artifacts | proof-required; independent checker required |
| C11 | EPRO/private-Merkle/work simulation | Explicit adjacent hybrids, distinct-input inventory, prequeries, collisions, adaptive later queries, canonical work, serialization/finalization/mutation | `lem:epro-complete-view` | hiding-closure and soundness/EPRO artifacts | proof-required |
| C12 | canonical proof identity and size | Canonical mined local proof only; schedule-dependent length is public | generated artifact table | release JSON `proof` object and proof bytes | artifact-green |
| C13 | default SBF identity and size | Fresh manifest-default local build; not a deployed-program statement | generated artifact table and Tier-2 byte rebuild | release JSON `default_production_sbf` object | artifact-green; clean reproduction required |
| C14 | verifier fits the CU cap locally | Worst literal tag-60 path in the pinned local Agave/runtime/heap/account context; evaluated, not theorem-derived | integrated CU reconciliation and Tier-3 replay | release JSON CU/headroom fields and production mutation KAT | artifact-green; independent replay required |
| C15 | one transaction | Exactly verification plus nullifier/pool mutation consuming a finalized, pre-uploaded proof account | transaction-scope definition and raw transaction | release JSON `scope` object | artifact-green locally; title/abstract qualifier mandatory |
| C16 | finalized proof account is required | Zero-sentinel and ownership checks in the frozen program; no intrinsic chain-level immutability claim | `lem:finalized-account-state-machine`; mutation/finalization matrix | source, release gates, Tier-1/Tier-3 tests | proof-required |
| C17 | atomic nullifier and pool transition | Verify-before-write order, precondition recheck, exact post-images, rollback and lock assumptions | `prop:atomic-refinement`; raw validator account images | production mutation KAT and adversarial tests | artifact-green; proposition/replay required |
| C18 | configured local program address | Address belongs to the frozen local configuration only | generated artifact table | source/build configuration | artifact-green; never use as deployment evidence |
| C19 | deployed/mainnet result | Successful finalized transaction bound to exact ProgramData/SBF/proof/accounts/CU | immutable mainnet evidence object | none yet | blocked |
| C20 | historical priority or “first” | Exact qualified claim only after mainnet gate and publication-day rescan | dated novelty method and evidence | novelty artifact plus future mainnet evidence | blocked |
| C21 | audited or production-ready | Requires independent audit and operational readiness evidence beyond tests | external reports | none | blocked |
| C22 | setup lifecycle cost | Account creation, chunks, readback, finalization, transactions, CU, fees, rent/storage, latency | lifecycle experiment table | new raw Tier-3/Tier-5 artifacts | experiment-required |
| C23 | prover/miner cost | Wall time, memory, q3 attempts, Abort rate, PoW mining, complete time-to-spend | prover/miner experiment table | new raw Tier-5 artifacts | experiment-required |
| C24 | throughput and contention | Same/different nullifier and pool workloads; writable locks, per-slot throughput and DoS limitations | contention experiment table | new raw validator artifacts | experiment-required |
| C25 | program immutability | Requires Program/ProgramData linkage, byte identity, capacity, finalized slot, and no upgrade authority | finalized-account theorem assumption plus deployment evidence | none for a deployment | blocked; local paper must state upgrade assumption |

<!-- markdownlint-enable MD013 -->

## Authoring rule

Every abstract sentence, contribution bullet, theorem conclusion, table
caption, and quantitative evaluation sentence must cite at least one matrix
ID in source comments. Before submission, a generated audit checks that every
used ID exists, that no `blocked` ID appears as an affirmative claim, and that
numeric claims are macros derived from the canonical release manifest rather
than copied from this scaffold.
