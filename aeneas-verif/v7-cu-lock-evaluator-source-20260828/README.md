# V7 selected evaluator CU-lock source bridge

This bundle pins the selected evaluator sparsity implementation at
`cee5947cbd5929a2be96d8f7ec29728afec2d3dd` and connects its literal source
schedules to
`AspisFormal/Pool/V7SelectedEvaluatorSparsitySourceBridge.lean`.

Nothing in `crates/`, `programs/`, the relation, the wire grammar, or the
transcript was changed.  The bundle is evidence and replay machinery only.

## Coverage

| Selected feature | Production root/table pinned by extraction | Kernel endpoint |
| --- | --- | --- |
| `v7-gamma-four-slot-block-audit` | `gamma_combine_v6_c1_four_slot_block` | four slots, six width-4 chunks plus width-2 tail; `gammaSelected_eq_literal` |
| packed range/shared selector | `add_preweighted_shared_selector`, caller interval 49/33 | nine groups; `rangeSelected_eq_literal` |
| packed digest selector tensor | `add_digest_binding_packed_selector_tensor`, `public_digest_packed_selector_tensor` LLBC | exact dynamic binding schedule, locals 0/11/12; `digestSelected_eq_literal` |
| active-mask basis | public root `pool_v1_pair_forest_copy_active_at_point_compiled_v1`, exact 64-mask constant | exact seven-way classification; `activeSelected_eq_literal` |
| Copy selector tensor | accumulator LLBC, 30 group/local entries, 43 pattern/local entries, 136 `COPY_LINKS` | 272 endpoint events; `copySelected_eq_literal` |
| Copy tag four-product dot | `copy_tag_coordinate_dot`, exact built offsets/terms | `copyTagFourProductDot_lt_u64` and `copyTagFourProductDot_reduce_exact` |
| Copy finish batching | `finish_selector_tensor_basis`, offsets `[0,9,15,26,30]` | widths 9/6/11/4; `finishSelected_eq_literal` |

The strongest theorem is
`selected_preserves_literal_evaluator_result`.  It first proves the stronger
structure equality `selectedPieces_eq_literalPieces`: all range, digest,
active, Copy, gamma, and finish values handed to the unchanged evaluator are
identical.  Applying any unchanged downstream evaluator to those structures
therefore preserves its literal result.

## Trust and exact remaining boundary

Charon produced clean LLBC (`has_errors = false`) for every root.  Aeneas
produced Lean for the gamma, range, active-mask public root, Copy tag dot,
Copy finish loop, constants, built tag schedule, and all 136 Copy links.

Aeneas' current symbolic borrow join cannot translate the two mutating slice
helpers `add_digest_binding_packed_selector_tensor` and
`accumulate_endpoint_selector_tensor_basis`; the clean Charon translation for
both is retained in `extraction/V7CuLockLeaves.llbc`.  Therefore the exact
remaining mechanical boundary is review (or a future Aeneas borrow-model
improvement) from those two LLBC bodies to the source-shaped event functions
universally quantified by the kernel theorem.  There is no mathematical,
cryptographic, table, feature, or evaluator-result assumption in the Lean
theorem itself.

The `FunsExternal_Template.lean` files are uninstantiated Aeneas output and
are not imported by AspisFormal.  The capstone uses no generated external
axiom.  Its `#print axioms` output is only `propext`, `Classical.choice`, and
`Quot.sound`; it contains no `sorryAx` or project-specific axiom.

## Replay

From a clean checkout at the pinned commit on `dombarker@nuc.local`:

```bash
systemd-run --user --scope --collect \
  --unit=aspis-v7-cu-lock-extraction-replay \
  -p MemoryHigh=22G -p MemoryMax=28G -p MemorySwapMax=0 \
  ./aeneas-verif/v7-cu-lock-evaluator-source-20260828/replay-extraction-nuc.sh \
  "$PWD" /tmp/v7-cu-lock-extraction-replay
```

Replay the ordinary-kernel proof from `AspisFormal/`:

```bash
systemd-run --user --scope --collect \
  --unit=aspis-v7-cu-lock-lean-replay \
  -p MemoryHigh=22G -p MemoryMax=28G -p MemorySwapMax=0 \
  /usr/bin/time -v lake env lean \
  AspisFormal/Pool/V7SelectedEvaluatorSparsitySourceBridge.lean
```

The measured final capstone replay used 6,708,668 KiB peak RSS, 9.18 s
wall time, and zero swaps.  Focused Charon/Aeneas maxima were 759,500 KiB
(range), 718,616 KiB (active public), 713,568 KiB (Copy core), and 644,648
KiB (gamma), all with zero swaps.

Run `./aeneas-verif/v7-cu-lock-evaluator-source-20260828/verify-pins.sh`
from the repository root to check revision, production hashes, LLBC status,
generated schedule sentinels, and forbidden proof constructs.
