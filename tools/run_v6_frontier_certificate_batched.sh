#!/usr/bin/env bash
set -euo pipefail

# Build the generated compact-frontier certificate without allowing Lake's
# dependency scheduler to launch every same-depth chunk at once.  Individual
# chunks can require several GiB while kernel-checking arithmetic, so a bounded
# batch is the reproducible release shape on a 64-GiB build host.

certificate_root=${1:-$(pwd)}
# Concrete-support generation keeps the formerly pathological depth-13 fringe
# cell at 6.54 GiB and 3.86 seconds by enumerating its six/seven live points
# before arithmetic.  Four same-depth chunks retain useful parallelism through
# depth 11.  Depths 12--18 are requested one depth at a time with Lake's worker
# count pinned to two: this avoids hundreds of scheduler restarts while keeping
# at most two high-depth cells live.  The enclosing zero-swap cgroup remains the
# authoritative hard limit.
batch_size=${2:-4}

if [[ ! $batch_size =~ ^[1-9][0-9]*$ ]]; then
  echo "batch size must be a positive integer" >&2
  exit 2
fi

source_dir="$certificate_root/AspisFormal/V6CompactFrontierTailCertificate"

if [[ ! -d $source_dir || ! -f $certificate_root/lakefile.toml ]]; then
  echo "not an AspisFormal certificate workspace: $certificate_root" >&2
  exit 2
fi

build_batch=()

flush_batch() {
  if ((${#build_batch[@]} == 0)); then
    return
  fi
  lake --log-level=error build "${build_batch[@]}"
  build_batch=()
}

cd "$certificate_root"

for depth_number in $(seq 0 18); do
  depth=$(printf '%02d' "$depth_number")
  if ((depth_number >= 12)); then
    lake -Kjobs=2 --log-level=error build \
      "AspisFormal.V6CompactFrontierTailCertificate.Depth${depth}"
    continue
  fi
  depth_batch_size=$batch_size
  while IFS= read -r source_file; do
    chunk=${source_file##*/}
    chunk=${chunk%.lean}
    build_batch+=("AspisFormal.V6CompactFrontierTailCertificate.$chunk")
    if ((${#build_batch[@]} == depth_batch_size)); then
      flush_batch
    fi
  done < <(find "$source_dir" -maxdepth 1 -type f \
    -name "Depth${depth}Chunk*.lean" -print | LC_ALL=C sort)
  flush_batch
  lake --log-level=error build \
    "AspisFormal.V6CompactFrontierTailCertificate.Depth${depth}"
done

# Only frontiers 210--224 are live at depth 18/selection 16.  Check their
# weighted tail in one worker; the public wrapper discharges 225--288 from the
# exact support theorem instead of importing 64 zero-cell proofs into the
# normalizer.
lake -Kjobs=1 --log-level=error build \
  AspisFormal.V6CompactFrontierTailCertificate.TailSumLive
lake -Kjobs=1 --log-level=error build \
  AspisFormal.V6CompactFrontierTailCertificate
lake --log-level=error build AspisFormal.V7CompactFrontierCertificate
