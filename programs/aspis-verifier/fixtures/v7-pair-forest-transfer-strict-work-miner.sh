#!/bin/sh
set -eu

# Fixture regeneration only. This wrapper deliberately persists transcript
# states and sequential progress, so it must not be used for an unpublished
# production wallet attempt. The frozen KAT is public and has no such privacy
# requirement.
: "${ASPIS_POW_METAL_BIN:?set ASPIS_POW_METAL_BIN}"
: "${ASPIS_POW_METAL_CHECKPOINT_DIR:?set ASPIS_POW_METAL_CHECKPOINT_DIR}"
: "${ASPIS_POW_METAL_LOG:?set ASPIS_POW_METAL_LOG}"

state=
bits=
previous=
for argument in "$@"; do
    case "$previous" in
        state) state=$argument ;;
        bits) bits=$argument ;;
    esac
    case "$argument" in
        --state) previous=state ;;
        --bits) previous=bits ;;
        *) previous= ;;
    esac
done

[ "${#state}" -eq 64 ] || { printf '%s\n' 'missing canonical --state' >&2; exit 2; }
[ -n "$bits" ] || { printf '%s\n' 'missing --bits' >&2; exit 2; }

mkdir -p "$ASPIS_POW_METAL_CHECKPOINT_DIR"
checkpoint="$ASPIS_POW_METAL_CHECKPOINT_DIR/pow-$bits-$state.checkpoint"
printf 'START bits=%s state=%s checkpoint=%s utc=%s\n' \
    "$bits" "$state" "$checkpoint" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$ASPIS_POW_METAL_LOG"
"$ASPIS_POW_METAL_BIN" "$@" --checkpoint "$checkpoint" --resume 2>> "$ASPIS_POW_METAL_LOG"
status=$?
printf 'END bits=%s state=%s status=%s utc=%s\n' \
    "$bits" "$state" "$status" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$ASPIS_POW_METAL_LOG"
exit "$status"
