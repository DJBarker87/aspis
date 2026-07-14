#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
output=${1:-"$root/target/release/aspis-pow-metal"}
mkdir -p "$(dirname -- "$output")"
xcrun swiftc -O -whole-module-optimization \
    -framework Foundation -framework CryptoKit -framework Metal \
    "$root/tools/aspis-pow-metal.swift" -o "$output"
printf '%s\n' "$output"
