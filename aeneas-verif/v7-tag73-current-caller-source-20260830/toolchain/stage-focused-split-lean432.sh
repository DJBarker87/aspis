#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 2; then
  echo "usage: $0 RAW_ROOT STAGED_ROOT" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
raw_root=$1
staged_root=$2
caller=V7AuthenticateFoldGammaOpaque
literal=V7GammaSlotMajorLiteral

test -f "$raw_root/$caller/Types.lean"
test -f "$raw_root/$caller/Funs.lean"
test -f "$raw_root/$literal/Types.lean"
test -f "$raw_root/$literal/Funs.lean"
test ! -e "$staged_root"

mkdir -p "$staged_root/$caller" "$staged_root/$literal"
cp "$raw_root/$caller"/*.lean "$staged_root/$caller/"
cp "$raw_root/$literal"/*.lean "$staged_root/$literal/"

cp "$script_dir/V7Tag73ExactTypesExternal.lean" \
  "$staged_root/$caller/TypesExternal.lean"
cp "$script_dir/V7Tag73MutableIteratorCompat.lean" \
  "$staged_root/$literal/MutableIteratorCompat.lean"

sed \
  -e "s/@MODULE@Generated/${caller}Generated/g" \
  -e "s/@MODULE@/${caller}/g" \
  "$script_dir/V7Tag73ExactFunsExternal.lean.in" \
  > "$staged_root/$caller/FunsExternal.lean"

# The reusable support was originally emitted for a split namespace which
# provided an additional `...Generated` alias.  This focused extraction emits
# its types directly in `$caller`, so no such namespace exists or is needed.
perl -0pi -e "s/^open ${caller}Generated\\n//m" \
  "$staged_root/$caller/FunsExternal.lean"

perl -0pi -e \
  "s/^import ${caller}\\.Types\\n/import ${caller}.Types\\nimport ${literal}.Funs\\n/m" \
  "$staged_root/$caller/FunsExternal.lean"

sed -e "s/@MODULE@/${caller}/g" \
  "$script_dir/V7AuthenticateFoldGammaOpaqueExtraExternal.lean.in" \
  >> "$staged_root/$caller/FunsExternal.lean"
cat "$script_dir/V7AuthenticateFoldGammaOpaqueSplit.lean.in" \
  >> "$staged_root/$caller/FunsExternal.lean"

for source in "$staged_root/$caller"/*.lean "$staged_root/$literal"/*.lean; do
  perl -0pi -e \
    's/^import Aeneas\n/import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n/m' \
    "$source"
done

caller_funs="$staged_root/$caller/Funs.lean"
test "$(shasum -a 256 "$raw_root/$caller/Funs.lean" | awk '{print $1}')" = \
  069118cd17c5eaab78997c08aed37f64121112738b1a092e3981c98966eb2a42
perl "$script_dir/chunk-aeneas-circle-tables.pl" "$caller_funs" "$caller"
test "$(wc -l < "$staged_root/$caller/CircleTableCompileOrder.txt" | tr -d ' ')" = 61
test "$(wc -l < "$staged_root/$caller/CircleTableLastModules.txt" | tr -d ' ')" = 5
test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next' \
  "$caller_funs")" = 1
perl -0pi -e \
  's/next := core\.slice\.iter\.IteratorIterMut\.next\n/next := core.slice.iter.IteratorIterMut.next_without_writeback\n/' \
  "$caller_funs"
test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next_without_writeback' \
  "$caller_funs")" = 1

perl -0pi -e \
  "s/^import ${literal}\\.Types\\n/import ${literal}.Types\\nimport ${literal}.MutableIteratorCompat\\n/m" \
  "$staged_root/$literal/Funs.lean"

literal_funs="$staged_root/$literal/Funs.lean"
test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next' \
  "$literal_funs")" = 1
test "$(rg -F -c 'let im1 := enumerate_back back' "$literal_funs")" = 1
test "$(rg -F -c 'core.iter.adapters.enumerate.IteratorEnumerate.next' \
  "$literal_funs")" = 1

perl -0pi -e \
  's/next := core\.slice\.iter\.IteratorIterMut\.next\n/next := core.slice.iter.IteratorIterMut.next_without_writeback\n/' \
  "$literal_funs"
perl -0pi -e \
  's/core\.iter\.adapters\.enumerate\.IteratorEnumerate\.next\n      \(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n      field\.QM31\) iter/core.iter.adapters.enumerate.IteratorEnumerateMut.next iter/' \
  "$literal_funs"
perl -0pi -e \
  's/core\.iter\.traits\.iterator\.Iterator\.enumerate\.trait_default\n      \(core\.slice\.iter\.IterMut\.Insts\.CoreIterTraitsIteratorIteratorMutAT\n      field\.QM31\) im/core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im/' \
  "$literal_funs"
perl -0pi -e \
  's/let im1 := enumerate_back back/let im1 := enumerate_back (back iter)/' \
  "$literal_funs"

test "$(rg -F -c 'next := core.slice.iter.IteratorIterMut.next_without_writeback' \
  "$literal_funs")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.next iter' "$literal_funs")" = 1
test "$(rg -F -c 'IteratorEnumerateMut.enumerate im' "$literal_funs")" = 1
test "$(rg -F -c 'let im1 := enumerate_back (back iter)' "$literal_funs")" = 1

# Lean's default parallel elaboration retains all of this generated module's
# large circle-table literals at once.  The unchunked 4,553-line file reached
# the focused 8 GiB hard cap even with one elaboration worker.  Split only at
# declaration boundaries and preserve byte-for-byte declaration order.  Each
# chunk imports the preceding chunk, so the resulting environment is exactly
# the same while the elaborator can release the syntax/term graph between
# chunks.
body_start=$(rg -n -F "namespace $caller" "$caller_funs" | cut -d: -f1)
body_end=$(rg -n -F "end $caller" "$caller_funs" | cut -d: -f1)
test -n "$body_start"
test -n "$body_end"
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

test "$(find "$staged_root/$caller" -name 'FunsChunk*.lean' | wc -l | tr -d ' ')" = 10

compile_order="$staged_root/FocusedCompileOrder.txt"
cat > "$compile_order" <<EOF
$literal/MutableIteratorCompat.lean
$literal/Types.lean
$literal/Funs.lean
$caller/TypesExternal.lean
$caller/Types.lean
$caller/FunsExternal.lean
EOF
cat "$staged_root/$caller/CircleTableCompileOrder.txt" >> "$compile_order"
find "$staged_root/$caller" -name 'FunsChunk*.lean' -print | sort | \
  sed "s#^$staged_root/##" >> "$compile_order"
cat >> "$compile_order" <<EOF
$caller/Funs.lean
FocusedSplitAudit.lean
EOF

cat > "$staged_root/FocusedSplitAudit.lean" <<'EOF'
import V7AuthenticateFoldGammaOpaque.Funs

#print V7AuthenticateFoldGammaOpaque.gamma_combine_v6_c1_slot_major_split_exact
#print V7AuthenticateFoldGammaOpaque.v7_verifier.authenticate_and_fold_queries
#print axioms V7AuthenticateFoldGammaOpaque.gamma_combine_v6_c1_slot_major_split_exact
#print axioms V7AuthenticateFoldGammaOpaque.v7_verifier.authenticate_and_fold_queries
EOF

printf 'focused source-equivalent split staging: PASS\n'
