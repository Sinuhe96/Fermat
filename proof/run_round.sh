#!/bin/sh
# =====================================================================
# run_round.sh — ONE M1-lane compile round.
#
# It enforces the four mechanical parts of M1_LANE.md §1 so a round cannot
# forget them:
#   1. write the in-flight handshake  pipeline/03-lean/M1_inflight
#      (proof/watch_lane.sh reads it to latch STALL / OVERRUN),
#   2. run the compile inside the container, with stdout+stderr captured to a
#      CONTAINER-SIDE log (a failing exit-code echo through the shell bridge is
#      how this repo lost evidence before),
#   3. remove the handshake,
#   4. append one row to pipeline/03-lean/M1_rounds.tsv.
#
# usage (repo root, host):  sh proof/run_round.sh <round> <chunk> <step> <file>
# example:                  sh proof/run_round.sh 1 B-01 probe probes/M1-LANE.probe.lean
#
# <file> is relative to pipeline/03-lean (any path the harness can copy).
# The round's classification (F1-F4/S1) is left as PENDING in the ledger: that
# is the orchestrator's judgement after reading the log, never the script's.
# =====================================================================
set -u

if [ "$#" -ne 4 ]; then
  echo "usage: sh proof/run_round.sh <round> <chunk> <step> <file-rel-03-lean>" >&2
  exit 2
fi

ROUND="$1"
CHUNK="$2"
STEP="$3"
FILE="$4"

cd "$(dirname "$0")/.." || exit 1
LEAN=pipeline/03-lean
NAME="${CHUNK}-${STEP}"
LOG="$LEAN/${NAME}_round${ROUND}.log"

# MSYS/Git-bash rewrites a leading-slash ARGUMENT into a Windows path before
# docker sees it (`/workspace/proof/compile_lean.sh` became
# `C:/Program Files/Git/workspace/proof/compile_lean.sh`, exit 2, 0 s). This
# disables that conversion for every command in this script.
MSYS_NO_PATHCONV=1
export MSYS_NO_PATHCONV

START=$(date +%s)
printf '%s\t%s\t%s\n' "$ROUND" "$START" "$FILE" > "$LEAN/M1_inflight"

echo "== round $ROUND: $NAME ($FILE) — compiling, expect 250-400 s =="
docker compose exec -T lean sh /workspace/proof/compile_lean.sh "$FILE" > "$LOG" 2>&1
RC=$?

END=$(date +%s)
rm -f "$LEAN/M1_inflight"

ERRS=$(grep -c 'error' "$LOG" 2>/dev/null)
[ -z "$ERRS" ] && ERRS=0
DUR=$((END - START))
UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)

printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$ROUND" "$CHUNK" "$STEP" "$FILE" "$UTC" "$DUR" "$RC" "$ERRS" \
  "PENDING" "see $LOG" >> "$LEAN/M1_rounds.tsv"

echo "round=$ROUND exit=$RC secs=$DUR error_lines=$ERRS log=$LOG"
exit "$RC"
