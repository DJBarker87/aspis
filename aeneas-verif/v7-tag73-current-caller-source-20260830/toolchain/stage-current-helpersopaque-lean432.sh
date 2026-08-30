#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 2; then
  echo "usage: $0 RAW_ROOT STAGED_ROOT" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
raw_root=$1
staged_root=$2
caller=V7Tag73CurrentHelpersOpaque
gamma=V7GammaSlotMajorLiteral
dot=V7Qm31Dot3Reduced

for module in "$caller" "$gamma" "$dot"; do
  test -f "$raw_root/$module/Types.lean"
  test -f "$raw_root/$module/Funs.lean"
done
test -f "$raw_root/$caller/TypesExternal_Template.lean"
test -f "$raw_root/$caller/FunsExternal_Template.lean"
test -f "$raw_root/$dot/TypesExternal_Template.lean"
test -f "$raw_root/$dot/FunsExternal_Template.lean"
test ! -e "$staged_root"

mkdir -p \
  "$staged_root/$caller" \
  "$staged_root/$gamma" \
  "$staged_root/$dot"
cp "$raw_root/$caller"/*.lean "$staged_root/$caller/"
cp "$raw_root/$gamma"/*.lean "$staged_root/$gamma/"
cp "$raw_root/$dot"/*.lean "$staged_root/$dot/"

# The caller and separately translated dot-product helper need the same
# global models for Rust core types and functions.  Emit those executable
# models once, then make both generated namespaces import that one definition.
# This prevents duplicate global declarations without introducing an axiom.
cp "$script_dir/V7Tag73ExactTypesExternal.lean" \
  "$staged_root/$caller/TypesExternalBase.lean"
cat > "$staged_root/$caller/TypesExternal.lean" <<EOF
import $caller.TypesExternalBase
EOF
cat > "$staged_root/$dot/TypesExternal.lean" <<EOF
import $caller.TypesExternalBase
EOF

sed \
  -e "s/@MODULE@Generated/${caller}Generated/g" \
  -e "s/@MODULE@/${caller}/g" \
  "$script_dir/V7Tag73ExactFunsExternal.lean.in" \
  > "$staged_root/$caller/FunsExternalBase.lean"
perl -0pi -e "s/^open ${caller}Generated\n//m" \
  "$staged_root/$caller/FunsExternalBase.lean"

cat > "$staged_root/$dot/FunsExternal.lean" <<EOF
import $dot.Types
import $caller.FunsExternalBase
EOF

cat > "$staged_root/$caller/FunsExternal.lean" <<EOF
import $caller.FunsExternalBase
import $gamma.Funs
import $dot.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
EOF
sed -e "s/@CALLER@/${caller}/g" \
  "$script_dir/V7CurrentHelpersOpaqueSplit.lean.in" \
  >> "$staged_root/$caller/FunsExternal.lean"

cp "$script_dir/V7Tag73MutableIteratorCompat.lean" \
  "$staged_root/$gamma/MutableIteratorCompat.lean"

for source in \
    "$staged_root/$caller"/*.lean \
    "$staged_root/$gamma"/*.lean \
    "$staged_root/$dot"/*.lean; do
  perl -0pi -e \
    's/^import Aeneas\n/import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n/m' \
    "$source"
done

# Keep the independently translated gamma helper executable with the same
# mutable-iterator compatibility model already accepted by the source bundle.
gamma_funs="$staged_root/$gamma/Funs.lean"
perl -0pi -e \
  "s/^import ${gamma}\\.Types\\n/import ${gamma}.Types\\nimport ${gamma}.MutableIteratorCompat\\n/m" \
  "$gamma_funs"
test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next' \
  "$gamma_funs")" = 1
test "$(rg -F -c 'let im1 := enumerate_back back' "$gamma_funs")" = 1
test "$(rg -F -c 'core.iter.adapters.enumerate.IteratorEnumerate.next' \
  "$gamma_funs")" = 1
perl -0pi -e \
  's/next := core\.slice\.iter\.IteratorIterMut\.next\n/next := core.slice.iter.IteratorIterMut.next_without_writeback\n/' \
  "$gamma_funs"
perl -0pi -e \
  's/core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n      \(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n      field\.QM31\) iter/core.iter.adapters.enumerate.IteratorEnumerateMut.next iter/' \
  "$gamma_funs"
perl -0pi -e \
  's/core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n      \(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n      field\.QM31\) im/core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im/' \
  "$gamma_funs"
perl -0pi -e \
  's/let im1 := enumerate_back back/let im1 := enumerate_back (back iter)/' \
  "$gamma_funs"
test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next_without_writeback' \
  "$gamma_funs")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.next iter' "$gamma_funs")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.enumerate im' "$gamma_funs")" = 1
test "$(rg -F -c 'let im1 := enumerate_back (back iter)' "$gamma_funs")" = 1

caller_types="$staged_root/$caller/Types.lean"
expected_caller_types_sha=${EXPECTED_CALLER_TYPES_SHA:-e6258f7a420199d2e42e9e26ca90c344f1b76074ea45f032390f042767853bd9}
test "$(shasum -a 256 "$raw_root/$caller/Types.lean" | awk '{print $1}')" = \
  "$expected_caller_types_sha"

# The query closure is represented exactly by the captured hash callback and
# parsed wire.  Mark this generated type synonym reducible so the separately
# compiled consumer can see that representation without unfolding unrelated
# generated declarations.
test "$(rg -U -c '^def v7_verifier\.verify_v7_read_only_with_statement_digest\.closure_1 :=\n[[:space:]]+Slice \(Slice Std\.U8\) → Result \(Array Std\.U8 32#usize\) ×\n[[:space:]]+aspis_core\.v7_onefold\.V7CompactOneFoldWire' \
  "$caller_types")" = 1
perl -0pi -e \
  's/^def v7_verifier\.verify_v7_read_only_with_statement_digest\.closure_1 :=$/@[reducible]\ndef v7_verifier.verify_v7_read_only_with_statement_digest.closure_1 :=/m' \
  "$caller_types"
test "$(rg -F -c '@[reducible]' "$caller_types")" -ge 1
test "$(rg -U -c '@\[reducible\]\ndef v7_verifier\.verify_v7_read_only_with_statement_digest\.closure_1 :=' \
  "$caller_types")" = 1

# The generated closure captures `(hash, wire)`.  Aeneas emitted the function
# arrow without parentheses, which Lean parses as a function returning a pair.
# Restore the exact Rust closure-product representation before any consumer is
# compiled.
test "$(rg -U -c '@\[reducible\]\ndef v7_verifier\.verify_v7_read_only_with_statement_digest\.closure_1 :=\n[[:space:]]+Slice \(Slice Std\.U8\) → Result \(Array Std\.U8 32#usize\) ×\n[[:space:]]+aspis_core\.v7_onefold\.V7CompactOneFoldWire' \
  "$caller_types")" = 1
perl -0pi -e \
  's/(def v7_verifier\.verify_v7_read_only_with_statement_digest\.closure_1 :=\n[[:space:]]+)(Slice \(Slice Std\.U8\) → Result \(Array Std\.U8 32#usize\))( ×\n[[:space:]]+aspis_core\.v7_onefold\.V7CompactOneFoldWire)/$1($2)$3/' \
  "$caller_types"
test "$(rg -U -c '@\[reducible\]\ndef v7_verifier\.verify_v7_read_only_with_statement_digest\.closure_1 :=\n[[:space:]]+\(Slice \(Slice Std\.U8\) → Result \(Array Std\.U8 32#usize\)\) ×\n[[:space:]]+aspis_core\.v7_onefold\.V7CompactOneFoldWire' \
  "$caller_types")" = 1

caller_funs="$staged_root/$caller/Funs.lean"
expected_caller_funs_sha=${EXPECTED_CALLER_FUNS_SHA:-470d8c68c224b26f54db77276af71cbd89b196cdc65dd47d088105b61c8e4c9a}
test "$(shasum -a 256 "$raw_root/$caller/Funs.lean" | awk '{print $1}')" = \
  "$expected_caller_funs_sha"

# Source-equivalent Lean 4.32 compatibility rewrites, each guarded by the
# exact count in this frozen generated caller.
test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next' \
  "$caller_funs")" = 1
test "$(rg -F -c 'let im1 := enumerate_back back' "$caller_funs")" = 1
test "$(rg -U -c 'core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n[[:space:]]+aspis_core\.field\.QM31\) iter' \
  "$caller_funs")" = 3
test "$(rg -U -c 'core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT \(Array\n[[:space:]]+aspis_core\.field\.QM31 4#usize\)\) iter' \
  "$caller_funs")" = 1
test "$(rg -U -c 'core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n[[:space:]]+aspis_core\.field\.QM31\) im' \
  "$caller_funs")" = 3
test "$(rg -U -c 'core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n[[:space:]]+\(Array aspis_core\.field\.QM31 4#usize\)\) im' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/next := core\.slice\.iter\.IteratorIterMut\.next\n/next := core.slice.iter.IteratorIterMut.next_without_writeback\n/' \
  "$caller_funs"
perl -0pi -e \
  's/core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n[[:space:]]+aspis_core\.field\.QM31\) iter/core.iter.adapters.enumerate.IteratorEnumerateMut.next iter/g' \
  "$caller_funs"
perl -0pi -e \
  's/core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT \(Array\n[[:space:]]+aspis_core\.field\.QM31 4#usize\)\) iter/core.iter.adapters.enumerate.IteratorEnumerateMut.next iter/' \
  "$caller_funs"
perl -0pi -e \
  's/core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n[[:space:]]+aspis_core\.field\.QM31\) im/core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im/g' \
  "$caller_funs"
perl -0pi -e \
  's/core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n[[:space:]]+\(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n[[:space:]]+\(Array aspis_core\.field\.QM31 4#usize\)\) im/core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im/' \
  "$caller_funs"
perl -0pi -e \
  's/let im1 := enumerate_back back/let im1 := enumerate_back (back iter)/' \
  "$caller_funs"

test "$(rg -F -c 'ok (context.layout_factor_fingerprint = i)' \
  "$caller_funs")" = 15
perl -0pi -e \
  's/ok \(context\.layout_factor_fingerprint = i\)/ok (decide (context.layout_factor_fingerprint = i))/g' \
  "$caller_funs"
test "$(rg -F -c 'ok (i = aspis_core.sumcheck.fold_binary_low_masks.CROSS_POSITIONS)' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/ok \(i = aspis_core\.sumcheck\.fold_binary_low_masks\.CROSS_POSITIONS\)/ok (decide (i = aspis_core.sumcheck.fold_binary_low_masks.CROSS_POSITIONS))/' \
  "$caller_funs"

test "$(rg -U -c 'aspis_core\.field\.QM31\.ZERO\n[[:space:]]+\(aspis_core\.field\.QM31\.add\)' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/aspis_core\.field\.QM31\.ZERO\n([[:space:]]+)\(aspis_core\.field\.QM31\.add\)/aspis_core.field.QM31.ZERO\n$1(fun p => aspis_core.field.QM31.add p.1 p.2)/' \
  "$caller_funs"

# The generated closure type retains the source array length as a phantom
# parameter, while its runtime representation is only `Slice U8`.  State the
# enclosing decoder's exact `N` explicitly instead of asking Lean to infer it
# from a value whose reduced type erases that index.
test "$(rg -U -c 'decode_packed_m31_eight_aligned\.closure\.Insts\.CoreOpsFunctionFnTupleUsizeU64\.call\n[[:space:]]+chunk' \
  "$caller_funs")" = 7
perl -0pi -e \
  's/(decode_packed_m31_eight_aligned\.closure\.Insts\.CoreOpsFunctionFnTupleUsizeU64\.call)\n([[:space:]]+)chunk/$1 (N := N)\n$2chunk/g' \
  "$caller_funs"
test "$(rg -U -c 'decode_packed_m31_eight_aligned\.closure\.Insts\.CoreOpsFunctionFnTupleUsizeU64\.call \(N := N\)\n[[:space:]]+chunk' \
  "$caller_funs")" = 7

test "$(rg -U -c '\) :\n  Result\n    \(aspis_core\.v6_transcript\.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context\.closure\n    TerminalCheck QueryFold\)\n  := do\n  ok c' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/\) :\n  Result\n    \(aspis_core\.v6_transcript\.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context\.closure\n    TerminalCheck QueryFold\)\n  := do\n  ok c/) :\n  Result\n    (Unit ×\n      aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure\n      TerminalCheck QueryFold)\n  := do\n  ok ((), c)/' \
  "$caller_funs"

# Two later no-op diagnostic callbacks have the same Aeneas FnMut arity
# artifact: source return `()` plus preserved closure state must translate to
# `(Unit, closure)`, not closure alone.
python3 "$script_dir/normalize-aeneas-noop-unit-fnmut.py" "$caller_funs"

test "$(rg -F -c 'toStr "' "$caller_funs")" = 6
test "$(rg -U -c 'toStr\n[[:space:]]+"' "$caller_funs")" = 3
perl -0pi -e \
  's/toStr "[^"]*"/(⟨[], Nat.zero_le _⟩ : Str)/g; s/toStr\n[[:space:]]+"[^"]*"/(⟨[], Nat.zero_le _⟩ : Str)/g' \
  "$caller_funs"

test "$(rg -U -c 'let a ←\n[[:space:]]+core\.result\.Result\.expect \(Box\.Insts\.CoreFmtDebug Global\n[[:space:]]+\(Slice\.Insts\.CoreFmtDebug aspis_core\.field\.QM31\.Insts\.CoreFmtDebug\)\) r[[:space:]]+\(\(⟨\[\], Nat\.zero_le _⟩ : Str\)\)' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/let a ←\n[[:space:]]+core\.result\.Result\.expect \(Box\.Insts\.CoreFmtDebug Global\n[[:space:]]+\(Slice\.Insts\.CoreFmtDebug aspis_core\.field\.QM31\.Insts\.CoreFmtDebug\)\) r[[:space:]]+\(\(⟨\[\], Nat\.zero_le _⟩ : Str\)\)/let a ←\n      match r with\n      | core.result.Result.Ok value => ok value\n      | core.result.Result.Err _ => fail .panic/' \
  "$caller_funs"

test "$(rg -F -c 'core.result.Result.expect core.fmt.DebugTryFromSliceError r ((⟨[], Nat.zero_le _⟩ : Str))' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/core\.result\.Result\.expect core\.fmt\.DebugTryFromSliceError r \(\(⟨\[\], Nat\.zero_le _⟩ : Str\)\)/match r with\n  | core.result.Result.Ok value => ok value\n  | core.result.Result.Err _ => fail .panic/' \
  "$caller_funs"

test "$(rg -F -c 'let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r' \
  "$caller_funs")" = 5
perl -0pi -e \
  's/let a ← core\.result\.Result\.unwrap core\.fmt\.DebugTryFromSliceError r/let a ←\n      match r with\n      | core.result.Result.Ok value => ok value\n      | core.result.Result.Err _ => fail .panic/g' \
  "$caller_funs"

test "$(rg -U -c 'let [[:alnum:]_]+ ←\n[[:space:]]+core\.result\.Result\.unwrap core\.fmt\.DebugTryFromSliceError [[:alnum:]_]+' \
  "$caller_funs")" = 6
perl -0pi -e \
  's/let ([[:alnum:]_]+) ←\n([[:space:]]+)core\.result\.Result\.unwrap core\.fmt\.DebugTryFromSliceError ([[:alnum:]_]+)/let $1 ←\n$2match $3 with\n$2| core.result.Result.Ok value => ok value\n$2| core.result.Result.Err _ => fail .panic/g' \
  "$caller_funs"

test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next_without_writeback' \
  "$caller_funs")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.next iter' "$caller_funs")" = 4
test "$(rg -F -c 'IteratorEnumerateMut.enumerate im' "$caller_funs")" = 4
test "$(rg -F -c 'let im1 := enumerate_back (back iter)' "$caller_funs")" = 1
test "$(rg -F -c 'ok (decide (context.layout_factor_fingerprint = i))' \
  "$caller_funs")" = 15
test "$(rg -U -c 'aspis_core\.field\.QM31\.ZERO\n[[:space:]]+\(fun p => aspis_core\.field\.QM31\.add p\.1 p\.2\)' \
  "$caller_funs")" = 1
test "$(rg -F -c 'ok ((), c)' "$caller_funs")" = 3
if rg -n 'toStr|core\.result\.Result\.(expect|unwrap)|(^|[^.[:alnum:]_])transcript\.(label|Transcript)' \
    "$caller_funs"; then
  echo "unexpected generated compatibility term remains" >&2
  exit 1
fi

# Aeneas emits this Rust array-length constant as a monadic slice operation
# even though its translated type is the pure scalar `Usize`.  Freeze the
# exact generated shape and replace it with the source-level fixed array
# length.  This is an extraction-only normalization: the immediately preceding
# constant is statically typed as a 15-entry array.
test "$(rg -U -c 'def\n[[:space:]]+aspis_statement\.atomic_state_only_terminal\.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS\n[[:space:]]+: Std\.Usize := do\n[[:space:]]+let s ←\n[[:space:]]+lift \(Array\.to_slice\n[[:space:]]+aspis_statement\.atomic_state_only_terminal\.constants\.ATOMIC_COPY_PATTERNS\)\n[[:space:]]+Slice\.len s' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/(def\n[[:space:]]+aspis_statement\.atomic_state_only_terminal\.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS\n)[[:space:]]+: Std\.Usize := do\n[[:space:]]+let s ←\n[[:space:]]+lift \(Array\.to_slice\n[[:space:]]+aspis_statement\.atomic_state_only_terminal\.constants\.ATOMIC_COPY_PATTERNS\)\n[[:space:]]+Slice\.len s/${1}  : Std.Usize := 15#usize/' \
  "$caller_funs"
test "$(rg -U -c 'def\n[[:space:]]+aspis_statement\.atomic_state_only_terminal\.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS\n[[:space:]]+: Std\.Usize := 15#usize' \
  "$caller_funs")" = 1

# The same Rust module later declares a field helper named `lift`, shadowing
# `Aeneas.Std.lift`, its unqualified monadic primitive.  Qualify the exact frozen suffix;
# translated calls to Rust functions are already fully qualified.
python3 "$script_dir/qualify-aeneas-result-lift-after-shadow.py" "$caller_funs"

# Validate and chunk the five large generated tables before any consumer is
# elaborated.  The chunker records hashes of the original tokens and expanded
# pairs and reconstructs the exact array at typed declaration boundaries.
perl "$script_dir/chunk-aeneas-circle-tables.pl" "$caller_funs" "$caller"
test "$(wc -l < "$staged_root/$caller/CircleTableCompileOrder.txt" | tr -d ' ')" = 61
test "$(wc -l < "$staged_root/$caller/CircleTableLastModules.txt" | tr -d ' ')" = 5

# The generated fifteen-entry atomic copy-pattern registry is another dense
# nested constant.  Preserve every emitted record token, compile one record per
# module, and reconnect them through one typed array so Lean can release each
# record's elaboration graph before compiling the production caller.
python3 "$script_dir/chunk-aeneas-atomic-patterns.py" \
  "$caller_funs" "$caller"
test "$(wc -l < "$staged_root/$caller/AtomicPatternCompileOrder.txt" | tr -d ' ')" = 16
test "$(wc -l < "$staged_root/$caller/AtomicPatternLastModule.txt" | tr -d ' ')" = 1
test "$(rg -c '^entry=[0-9][0-9] source_sha256=[0-9a-f]{64} expanded_sha256=[0-9a-f]{64}$' \
  "$staged_root/$caller/AtomicPatternChunkManifest.txt")" = 15
atomic_last_module=$(tr -d '\n' \
  < "$staged_root/$caller/AtomicPatternLastModule.txt")
test -n "$atomic_last_module"

# Exact executable models for the three remaining scalar intrinsics used by
# the production statement terminal.  They are staged separately so the
# already-compiled circle and atomic-table certificates remain reusable.
cat > "$staged_root/$caller/LateScalarExternal.lean" <<EOF
import $caller.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error

def core.num.trailingZerosNat : Nat → Nat → Nat
  | _, 0 => 0
  | value, fuel + 1 =>
    if value % 2 = 0 then 1 + core.num.trailingZerosNat (value / 2) fuel
    else 0

@[rust_fun "core::num::{u16}::trailing_zeros"]
def core.num.U16.trailing_zeros (value : Std.U16) : Result Std.U32 :=
  .ok ⟨BitVec.ofNat 32 (core.num.trailingZerosNat value.bv.toNat 16)⟩

@[rust_fun "core::num::{u64}::trailing_zeros"]
def core.num.U64.trailing_zeros (value : Std.U64) : Result Std.U32 :=
  .ok ⟨BitVec.ofNat 32 (core.num.trailingZerosNat value.bv.toNat 64)⟩

@[rust_fun "core::num::{u64}::count_ones"]
def core.num.U64.count_ones (value : Std.U64) : Result Std.U32 :=
  .ok ⟨value.bv.cpop.zeroExtend 32⟩
EOF

# Exact iterator constructors/folds first needed by caller chunk 19.  These
# definitions are the direct executable models of the corresponding Rust
# standard-library interfaces; no statement-terminal value is trusted.
cat > "$staged_root/$caller/LateIteratorExternal.lean" <<EOF
import $caller.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error

@[rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default
    {Self B F Item : Type}
    (_iteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (_fnMutInst : core.ops.function.FnMut F Item B) :
    Self → F → Result (core.iter.adapters.map.Map Self F)
  | iterator, closure => .ok ⟨iterator, closure⟩

@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::fold"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
    {I Acc F Item : Type}
    (doubleEndedIteratorInst :
      core.iter.traits.double_ended.DoubleEndedIterator I Item)
    (fnMutInst : core.ops.function.FnMut F (Acc × Item) Acc)
    (iterator : core.iter.adapters.rev.Rev I) (accumulator : Acc)
    (closure : F) : Result Acc := do
  let result : Acc × core.iter.adapters.rev.Rev I × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, innerNext) ←
          doubleEndedIteratorInst.next_back state.iter
        match item with
        | none => .ok (.done (acc, ⟨innerNext⟩, closureState))
        | some value =>
          let (accNext, closureNext) ←
            fnMutInst.call_mut closureState (acc, value)
          .ok (.cont (accNext, ⟨innerNext⟩, closureNext)))
      (accumulator, iterator, closure)
  .ok result.1

@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::RangeInclusive<@A>, @A>}::fold"]
def core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold
    {A Acc F : Type} (stepInst : core.iter.range.Step A)
    (fnMutInst : core.ops.function.FnMut F (Acc × A) Acc)
    (iterator : core.ops.range.RangeInclusive A) (accumulator : Acc)
    (closure : F) : Result Acc := do
  let result : Acc × core.ops.range.RangeInclusive A × F ←
    loop
      (fun (acc, state, closureState) => do
        let (item, stateNext) ←
          core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
            stepInst state
        match item with
        | none => .ok (.done (acc, stateNext, closureState))
        | some value =>
          let (accNext, closureNext) ←
            fnMutInst.call_mut closureState (acc, value)
          .ok (.cont (accNext, stateNext, closureNext)))
      (accumulator, iterator, closure)
  .ok result.1
EOF

# Split the remaining generated caller only at top-level declaration markers.
# Each chunk imports its predecessor, preserving declaration order while
# allowing Lean to release each earlier syntax graph.
body_start=$(rg -n -F "namespace $caller" "$caller_funs" | cut -d: -f1)
body_end=$(rg -n -F "end $caller" "$caller_funs" | cut -d: -f1)
test -n "$body_start"
test -n "$body_end"
test "$(printf '%s\n' "$body_start" | wc -l | tr -d ' ')" = 1
test "$(printf '%s\n' "$body_end" | wc -l | tr -d ' ')" = 1
body_start=$((body_start + 1))
body_end=$((body_end - 1))

marker_lines=()
while IFS= read -r marker; do
  line=$(rg -n -F "$marker" "$caller_funs" | cut -d: -f1)
  test -n "$line"
  test "$(printf '%s\n' "$line" | wc -l | tr -d ' ')" = 1
  marker_lines+=("$line")
done <<'EOF'
/-- [aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW]
/-- [aspis_core::circle_fri::V6_CIRCLE_LOW6_WINDOW]
/-- [aspis_core::circle_fri::V6_CIRCLE_MIDDLE6_WINDOW]
/-- [aspis_core::circle_fri::V6_CIRCLE_HIGH6_WINDOW]
/-- [aspis_core::params::CIRCLE_LOG_ORDER]
/-- [aspis_core::circle_fri::selected_circle_fiber_points_shared]: loop body 0:
/-- [aspis_core::v6_onefold::decode_packed_m31_eight_aligned]: loop body 0:
/-- [aspis_core::v6_onefold::prepare_v6_onefold_coordinates]: loop body 0:
/-- [aspis_core::v7_onefold::{aspis_core::v7_onefold::V7CompactOneFoldWire<'a>}::query]:
EOF

# The selected statement-terminal/current-caller suffix is dense enough that
# keeping every remaining declaration in one generated module drives Lean's
# retained elaboration graph toward the per-job memory ceiling.  Continue to
# split only at top-level generated declaration comments, eight declarations
# at a time.  This preserves declaration order and semantics while ensuring
# each focused target releases its syntax/elaboration graph before the next.
final_fixed_marker=${marker_lines[$(( ${#marker_lines[@]} - 1 ))]}
suffix_declarations=0
while IFS=: read -r line _; do
  if ((line <= final_fixed_marker)); then
    continue
  fi
  suffix_declarations=$((suffix_declarations + 1))
  if ((suffix_declarations > 8 && (suffix_declarations - 1) % 8 == 0)); then
    marker_lines+=("$line")
  fi
done < <(rg -n '^/-- \[' "$caller_funs")
test "$suffix_declarations" -gt 8

starts=("$body_start" "${marker_lines[@]}")
ends=()
for ((index = 1; index < ${#starts[@]}; index++)); do
  ends+=("$((starts[index] - 1))")
done
ends+=("$body_end")

for ((index = 0; index < ${#starts[@]}; index++)); do
  chunk=$(printf 'FunsChunk%02d' "$index")
  chunk_file="$staged_root/$caller/$chunk.lean"
  if ((index == 0)); then
    prerequisite="$caller.FunsExternal"
  else
    prerequisite=$(printf '%s.FunsChunk%02d' "$caller" "$((index - 1))")
  fi
  cat > "$chunk_file" <<EOF
import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import $caller.Types
import $prerequisite
EOF
  if ((index < 5)); then
    table_module=$(sed -n "$((index + 1))p" \
      "$staged_root/$caller/CircleTableLastModules.txt")
    test -n "$table_module"
    printf 'import %s\n' "$table_module" >> "$chunk_file"
  fi
  if ((index == 0)); then
    printf 'import %s\n' "$atomic_last_module" >> "$chunk_file"
    printf 'import %s\n' "$caller.LateScalarExternal" >> "$chunk_file"
  fi
  if ((index == 19)); then
    printf 'import %s\n' "$caller.LateIteratorExternal" >> "$chunk_file"
  fi
  cat >> "$chunk_file" <<EOF

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace $caller
EOF
  sed -n "${starts[index]},${ends[index]}p" "$caller_funs" >> "$chunk_file"
  printf '\nend %s\n' "$caller" >> "$chunk_file"
done

last_chunk=$(printf 'FunsChunk%02d' "$(( ${#starts[@]} - 1 ))")
cat > "$caller_funs" <<EOF
import $caller.$last_chunk
EOF
test "$(find "$staged_root/$caller" -name 'FunsChunk*.lean' | wc -l | tr -d ' ')" = \
  "${#starts[@]}"

compile_order="$staged_root/CurrentCallerCompileOrder.txt"
cat > "$compile_order" <<EOF
$caller/TypesExternalBase.lean
$caller/TypesExternal.lean
$caller/Types.lean
$caller/FunsExternalBase.lean
$gamma/MutableIteratorCompat.lean
$gamma/Types.lean
$gamma/Funs.lean
$dot/TypesExternal.lean
$dot/Types.lean
$dot/FunsExternal.lean
$dot/Funs.lean
$caller/FunsExternal.lean
EOF
cat "$staged_root/$caller/CircleTableCompileOrder.txt" >> "$compile_order"
cat "$staged_root/$caller/AtomicPatternCompileOrder.txt" >> "$compile_order"
printf '%s\n' "$caller/LateScalarExternal.lean" >> "$compile_order"
while IFS= read -r chunk_file; do
  if test "$(basename -- "$chunk_file")" = FunsChunk19.lean; then
    printf '%s\n' "$caller/LateIteratorExternal.lean" >> "$compile_order"
  fi
  printf '%s\n' "${chunk_file#"$staged_root/"}" >> "$compile_order"
done < <(find "$staged_root/$caller" -name 'FunsChunk*.lean' -print | sort)
cat >> "$compile_order" <<EOF
$caller/Funs.lean
CurrentCallerAudit.lean
EOF

cat > "$staged_root/CurrentCallerAudit.lean" <<EOF
import $caller.Funs

#print $caller.v7_verifier.verify_v7_read_only_with_statement_digest
#print $caller.aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_owned_v3
#print $caller.aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_owned_v3
#print $caller.gamma_combine_v6_c1_slot_major_split_exact
#print $caller.qm31_dot3_split_exact
#print axioms $caller.v7_verifier.verify_v7_read_only_with_statement_digest
#print axioms $caller.aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_owned_v3
#print axioms $caller.aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_owned_v3
#print axioms $caller.gamma_combine_v6_c1_slot_major_split_exact
#print axioms $caller.qm31_dot3_split_exact
#print axioms ${caller}HelpersSplit.gamma_input_components_exact
#print axioms ${caller}HelpersSplit.gamma_input_c1_limbs_exact
#print axioms ${caller}HelpersSplit.gamma_output_limbs_exact
#print axioms ${caller}HelpersSplit.dot_input_limbs_exact
#print axioms ${caller}HelpersSplit.dot_output_limbs_exact
#print axioms $gamma.v6_onefold.gamma_combine_v6_c1_slot_major
#print axioms $dot.field.qm31_dot3
EOF

printf 'current caller helper-split staging: PASS\n'
