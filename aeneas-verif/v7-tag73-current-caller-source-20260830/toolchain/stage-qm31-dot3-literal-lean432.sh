#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 2; then
  echo "usage: $0 RAW_ROOT STAGED_ROOT" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
raw_root=$1
staged_root=$2
module=V7Qm31Dot3Reduced

test -f "$raw_root/$module/Types.lean"
test -f "$raw_root/$module/Funs.lean"
test ! -e "$staged_root"

mkdir -p "$staged_root/$module"
cp "$raw_root/$module"/*.lean "$staged_root/$module/"
cp "$script_dir/V7Tag73ExactTypesExternal.lean" \
  "$staged_root/$module/TypesExternal.lean"
sed \
  -e "s/@MODULE@Generated/${module}Generated/g" \
  -e "s/@MODULE@/${module}/g" \
  "$script_dir/V7Tag73ExactFunsExternal.lean.in" \
  > "$staged_root/$module/FunsExternal.lean"
perl -0pi -e "s/^open ${module}Generated\n//m" \
  "$staged_root/$module/FunsExternal.lean"

for source in "$staged_root/$module"/*.lean; do
  perl -0pi -e \
    's/^import Aeneas\n/import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n/m' \
    "$source"
done

cat > "$staged_root/Qm31Dot3LiteralAudit.lean" <<'EOF'
import V7Qm31Dot3Reduced.Funs

#print V7Qm31Dot3Reduced.field.qm31_dot3
#print axioms V7Qm31Dot3Reduced.field.qm31_dot3
EOF

cat > "$staged_root/Qm31Dot3CompileOrder.txt" <<EOF
$module/TypesExternal.lean
$module/Types.lean
$module/FunsExternal.lean
$module/Funs.lean
Qm31Dot3LiteralAudit.lean
EOF

printf 'qm31_dot3 exact literal staging: PASS\n'
