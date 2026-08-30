#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 3; then
  echo "usage: $0 RAW_ROOT STAGED_ROOT MODULE" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
raw_root=$1
staged_root=$2
module=$3
raw_module="$raw_root/$module"
staged_module="$staged_root/$module"

test -f "$raw_module/Types.lean"
test -f "$raw_module/TypesExternal_Template.lean"
test -f "$raw_module/Funs.lean"
test -f "$raw_module/FunsExternal_Template.lean"
test ! -e "$staged_root"

mkdir -p "$staged_module"
cp "$raw_module"/*.lean "$staged_module/"
cp "$raw_module/TypesExternal_Template.lean" "$staged_module/TypesExternal.lean"
cp "$raw_module/FunsExternal_Template.lean" "$staged_module/FunsExternal.lean"
cp "$script_dir/V7Tag73MutableIteratorCompat.lean" \
  "$staged_module/MutableIteratorCompat.lean"

for source in "$staged_module"/*.lean; do
  perl -0pi -e \
    's/^import Aeneas\n/import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n/m' \
    "$source"
done

perl -0pi -e \
  "s/^import ${module}\\.FunsExternal\\n/import ${module}.FunsExternal\\nimport ${module}.MutableIteratorCompat\\n/m" \
  "$staged_module/Funs.lean"

test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next' \
  "$staged_module/Funs.lean")" = 1
test "$(rg -F -c 'let im1 := enumerate_back back' \
  "$staged_module/Funs.lean")" = 1

perl -0pi -e \
  's/next := core\.slice\.iter\.IteratorIterMut\.next\n/next := core.slice.iter.IteratorIterMut.next_without_writeback\n/' \
  "$staged_module/Funs.lean"
perl -0pi -e \
  's/core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n      \(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n      field\.QM31\) iter/core.iter.adapters.enumerate.IteratorEnumerateMut.next iter/' \
  "$staged_module/Funs.lean"
perl -0pi -e \
  's/core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n      \(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n      field\.QM31\) im/core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im/' \
  "$staged_module/Funs.lean"
perl -0pi -e \
  's/let im1 := enumerate_back back/let im1 := enumerate_back (back iter)/' \
  "$staged_module/Funs.lean"

# Aeneas represents Rust equality as a proposition. When such a result is
# stored and later used as a Rust `bool`, preserve the executable Boolean by
# deciding the equality at the binding site. The exact production root has
# five spend-factor and ten pool-factor bindings plus one low-mask binding.
test "$(rg -F -c 'ok (context.layout_factor_fingerprint = i)' \
  "$staged_module/Funs.lean")" = 15
perl -0pi -e \
  's/ok \(context\.layout_factor_fingerprint = i\)/ok (decide (context.layout_factor_fingerprint = i))/g' \
  "$staged_module/Funs.lean"
test "$(rg -F -c 'ok (i = sumcheck.fold_binary_low_masks.CROSS_POSITIONS)' \
  "$staged_module/Funs.lean")" = 1
perl -0pi -e \
  's/ok \(i = sumcheck\.fold_binary_low_masks\.CROSS_POSITIONS\)/ok (decide (i = sumcheck.fold_binary_low_masks.CROSS_POSITIONS))/' \
  "$staged_module/Funs.lean"

# Rust function items receive a tuple when used as `FnMut<(A, B), C>`.
test "$(rg -F -c 'field.QM31.ZERO (field.QM31.add)' \
  "$staged_module/Funs.lean")" = 1
perl -0pi -e \
  's/field\.QM31\.ZERO \(field\.QM31\.add\)/field.QM31.ZERO (fun p => field.QM31.add p.1 p.2)/' \
  "$staged_module/Funs.lean"

# The no-op diagnostic closure returns Rust unit together with its unchanged
# `FnMut` state. Aeneas emits only the latter in this one generated helper.
test "$(rg -U -c '\) :\n  Result\n    \(v6_transcript\.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context\.closure\n    TerminalCheck QueryFold\)\n  := do\n  ok c' \
  "$staged_module/Funs.lean")" = 1
perl -0pi -e \
  's/\) :\n  Result\n    \(v6_transcript\.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context\.closure\n    TerminalCheck QueryFold\)\n  := do\n  ok c/) :\n  Result\n    (Unit ×\n      v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure\n      TerminalCheck QueryFold)\n  := do\n  ok ((), c)/' \
  "$staged_module/Funs.lean"

test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next_without_writeback' \
  "$staged_module/Funs.lean")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.next iter' \
  "$staged_module/Funs.lean")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.enumerate im' \
  "$staged_module/Funs.lean")" = 1
test "$(rg -F -c 'let im1 := enumerate_back (back iter)' \
  "$staged_module/Funs.lean")" = 1
test "$(rg -F -c 'ok (decide (context.layout_factor_fingerprint = i))' \
  "$staged_module/Funs.lean")" = 15
test "$(rg -F -c 'field.QM31.ZERO (fun p => field.QM31.add p.1 p.2)' \
  "$staged_module/Funs.lean")" = 1
test "$(rg -F -c 'ok ((), c)' "$staged_module/Funs.lean")" = 1
if rg -n '\(transcript[[:space:]]*:' "$staged_module/Funs.lean"; then
  echo "generated local still shadows the transcript namespace" >&2
  exit 1
fi

printf 'Lean 4.32 generated staging: PASS\n'
