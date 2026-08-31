#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 GENERATED_CODEC_ROOT" >&2
  exit 2
fi

generated_root=$1
types_file="$generated_root/V7PairForestProductionCodecs/Types.lean"
funs_file="$generated_root/V7PairForestProductionCodecs/Funs.lean"
externals_file="$generated_root/V7PairForestProductionCodecs/FunsExternal.lean"

types_count=$(grep -o 'solana_program_error\.ProgramError' "$types_file" | wc -l | tr -d ' ')
funs_count=$(grep -o 'solana_program_error\.ProgramError' "$funs_file" | wc -l | tr -d ' ')

if [[ "$types_count" != 27 || "$funs_count" != 22 ]]; then
  echo "unexpected generated identifier inventory: Types=$types_count Funs=$funs_count" >&2
  exit 1
fi

funs_option_count=$(grep -o \
  'core\.option\.Option\.Insts\.CoreCmpPartialEqOption\.eq' \
  "$funs_file" | wc -l | tr -d ' ')
externals_option_count=$(grep -o \
  'core\.option\.Option\.Insts\.CoreCmpPartialEqOption\.eq' \
  "$externals_file" | wc -l | tr -d ' ')

if [[ "$funs_option_count" != 1 || "$externals_option_count" != 1 ]]; then
  echo "unexpected generated Option equality inventory: Funs=$funs_option_count FunsExternal=$externals_option_count" >&2
  exit 1
fi

perl -pi -e \
  's/solana_program_error\.ProgramError/solana_program_error.CodecProgramError/g' \
  "$types_file" "$funs_file"

perl -pi -e \
  's/core\.option\.Option\.Insts\.CoreCmpPartialEqOption\.eq/V7PairForestCodecOptionEq/g' \
  "$funs_file" "$externals_file"

if grep -q 'solana_program_error\.ProgramError' "$types_file" "$funs_file"; then
  echo "unrenamed generated ProgramError identifier remains" >&2
  exit 1
fi

if grep -q 'core\.option\.Option\.Insts\.CoreCmpPartialEqOption\.eq' \
    "$funs_file" "$externals_file"; then
  echo "unrenamed generated Option equality identifier remains" >&2
  exit 1
fi
