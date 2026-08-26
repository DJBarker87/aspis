#!/usr/bin/env bash
set -euo pipefail
backend=/home/dombarker/project-offloads/aeneas-d860-v6/backends/lean
workspace=/home/dombarker/project-offloads/aspis-v7-k12-merkle-source-20260826/caller-lean-compile-01/workspace
export LEAN_NUM_THREADS=1
export LEAN_PATH="$backend:$workspace"
cd "$backend"
for module_name in TypesExternal Types FunsExternal; do
  /home/dombarker/.elan/bin/lake env lean -j1 -R "$workspace" -o "$workspace/V7MerkleK12/$module_name.olean" "$workspace/V7MerkleK12/$module_name.lean"
done
for module_name in TypesExternal Types FunsExternal Funs; do
  /home/dombarker/.elan/bin/lake env lean -j1 -R "$workspace" -o "$workspace/V7MerkleCaller/$module_name.olean" "$workspace/V7MerkleCaller/$module_name.lean"
done
