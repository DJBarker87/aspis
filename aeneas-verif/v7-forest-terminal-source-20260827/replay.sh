#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
"$script_dir/replay-extraction.sh"
"$script_dir/replay-lean.sh"
