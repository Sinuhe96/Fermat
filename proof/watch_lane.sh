#!/usr/bin/env bash
# =====================================================================
# watch_lane.sh — mechanical watchdog for the Fermat main-proof (M1) lane
#
# It judges NOTHING about mathematics. It samples the environment and
# latches stall / contention / host failures that the orchestrator must
# read BEFORE every compile round (AGENTS.md: "if it is red, fix the
# machine, not the math").
#
# Handshake (paths relative to the repo root):
#   pipeline/03-lean/M1_inflight   orchestrator writes "<round>\t<epoch>\t<file>"
#                                  immediately before a compile round and
#                                  deletes it once the round's log is saved.
#   pipeline/03-lean/M1_watch.log  append-only: HB / LATCH / REPORT lines.
#
# Latch kinds: ENV-DOWN | CONTENTION | STALL | OVERRUN | DISK | OVERBUDGET
#   One latch per episode (fired on entry into the bad state, never repeated
#   while it persists). The orchestrator records "ACK <seq>" after acting.
#   OVERBUDGET fires once the lane has run >= BUDGET seconds since THIS script
#   launch: the orchestrator must stop before the next round and report. A
#   resumed session relaunches this script, so the budget is re-based to a
#   fresh window from that launch.
#
# Env overrides: ROOT TICK REPORT_EVERY STALL_AFTER OVERRUN_AFTER BUDGET
#   REPORT_EVERY defaults to 1800 (30 min) — the progress-report cadence.
#   BUDGET defaults to 7200 (2 h wall clock); 0 disables the time budget.
# =====================================================================
set -u

ROOT="${ROOT:-$(pwd)}"
cd "$ROOT" || exit 1
LEAN_DIR="$ROOT/pipeline/03-lean"
WATCHLOG="$LEAN_DIR/M1_watch.log"
INFLIGHT="$LEAN_DIR/M1_inflight"
TICK="${TICK:-60}"
REPORT_EVERY="${REPORT_EVERY:-1800}"
STALL_AFTER="${STALL_AFTER:-900}"
OVERRUN_AFTER="${OVERRUN_AFTER:-1500}"
BUDGET="${BUDGET:-7200}"   # wall-clock budget for one run (default 2 h); 0 disables

mkdir -p "$LEAN_DIR"

log() { printf '%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$1" >> "$WATCHLOG"; }

# Prints "<lakes> <leans>: the number of processes named exactly `lake` and `lean`
# inside the container, so the caller can tell ONE round (1 lake + 1..N lean
# workers, which is what `lake env lean` costs) from TWO (>= 2 lakes).
count_procs() {
  docker compose exec -T lean sh -c 'l=0; n=0; for c in /proc/[0-9]*/comm; do t=$(cat "$c" 2>/dev/null); case "$t" in lake) l=$((l+1));; lean) n=$((n+1));; esac; done; echo "$l $n"' 2>/dev/null | tr -d '\r' | tail -n 1
}

iso() { date -u +%Y-%m-%dT%H:%M:%SZ; }

printf 'WATCHDOG-READY lane=M1 tick=%ss report=%ss stall=%ss overrun=%ss budget=%ss root=%s\n' \
  "$TICK" "$REPORT_EVERY" "$STALL_AFTER" "$OVERRUN_AFTER" "$BUDGET" "$ROOT"
log "WATCHDOG-START	tick=$TICK	report=$REPORT_EVERY	stall=$STALL_AFTER	overrun=$OVERRUN_AFTER	budget=$BUDGET"

prev=""
seq=0
ticks=0
maxage=0
START_EPOCH=$(date +%s)
report_at=$(( START_EPOCH + REPORT_EVERY ))

while :; do
  now=$(date +%s)
  ticks=$((ticks + 1))
  raw=$(count_procs)
  cond=""
  detail=""
  elapsed=$((now - START_EPOCH))
  if [ "$BUDGET" -gt 0 ]; then
    budget_left=$(( BUDGET - elapsed ))
    [ "$budget_left" -lt 0 ] && budget_left=0
  else
    budget_left=-
  fi

  # OVERBUDGET outranks every other condition: once the window is spent, stop
  # before the next round regardless of contention/stall/disk state.
  if [ "$BUDGET" -gt 0 ] && [ "$elapsed" -ge "$BUDGET" ]; then
    cond=OVERBUDGET
    detail="lane budget ${BUDGET}s elapsed (${elapsed}s) — hard stop: start no new round"
  else
  case "$raw" in
    [0-9]*" "[0-9]*)
      lakes=${raw%% *}
      leans=${raw##* }
      if [ "$lakes" -gt 1 ]; then
        cond=CONTENTION
        detail="$lakes lake processes in container (a second compile round)"
      elif [ ! -f "$INFLIGHT" ] && [ $((lakes + leans)) -gt 0 ]; then
        cond=CONTENTION
        detail="compiler running ($lakes lake / $leans lean) with no in-flight marker: another lane or session"
      fi
      if [ -f "$INFLIGHT" ]; then
        rnd=$(cut -f1 "$INFLIGHT" 2>/dev/null)
        t0=$(cut -f2 "$INFLIGHT" 2>/dev/null)
        case "$t0" in
          ''|*[!0-9]*) t0=$now ;;
        esac
        age=$((now - t0))
        [ "$age" -gt "$maxage" ] && maxage=$age
        if [ "$age" -gt "$OVERRUN_AFTER" ]; then
          cond=OVERRUN
          detail="round $rnd running ${age}s > ${OVERRUN_AFTER}s"
        elif [ "$age" -gt "$STALL_AFTER" ] && [ "$lakes" -eq 0 ]; then
          cond=STALL
          detail="round $rnd ${age}s with 0 lake processes (hung or dead)"
        fi
      fi
      ;;
    *)
      cond=ENV-DOWN
      detail="container exec failed (docker/engine/container)"
      ;;
  esac
  fi

  if [ -z "$cond" ] && [ $((ticks % 10)) -eq 0 ]; then
    free=$(df -Pk "$LEAN_DIR" 2>/dev/null | tail -n 1 | awk '{gsub(/%/,"",$5); print $5}')
    case "$free" in
      ''|*[!0-9]*) : ;;
      *) if [ "$free" -ge 95 ]; then cond=DISK; detail="host volume ${free}% full"; fi ;;
    esac
  fi

  if [ -n "$cond" ] && [ "$cond" != "$prev" ]; then
    seq=$((seq + 1))
    log "LATCH	$seq	$cond	$detail"
    printf 'LATCH seq=%s kind=%s detail=%s at=%s\n' "$seq" "$cond" "$detail" "$(iso)"
  fi
  prev="$cond"

  if [ -f "$INFLIGHT" ]; then
    st="R$(cut -f1 "$INFLIGHT" 2>/dev/null)@$((now - $(cut -f2 "$INFLIGHT" 2>/dev/null)))s"
  else
    st="-"
  fi
  # This lane's round logs are `<chunk>-<step>_round<N>.log` (`run_round.sh`), and
  # the older lanes' are `*_compile_*.log`.  Globbing only the latter reported a
  # ~14 h-old age while rounds were running minutes ago (the latch logic does not
  # read this value, but a stale metric is worse than none).
  newest=$(ls -t "$LEAN_DIR"/*compile*.log "$LEAN_DIR"/*_round*.log 2>/dev/null | head -n 1)
  if [ -n "$newest" ]; then
    la=$(( now - $(date -r "$newest" +%s) ))
  else
    la=-1
  fi
  log "HB	$ticks	proc=$raw	state=$st	left=${budget_left}s	latched=${cond:-none}	lastlog=${la}s"
  printf 'HB %s proc=%s state=%s left=%ss latch=%s lastlog=%ss\n' "$ticks" "$raw" "$st" "$budget_left" "${cond:-none}" "$la"

  if [ "$now" -ge "$report_at" ]; then
    log "REPORT	ticks=$ticks	max_inflight_age=${maxage}s	budget_left=${budget_left}s	latched=${cond:-none}	seq=$seq"
    printf 'REPORT ticks=%s max_inflight_age=%ss budget_left=%ss latch=%s seq=%s at=%s\n' \
      "$ticks" "$maxage" "$budget_left" "${cond:-none}" "$seq" "$(iso)"
    maxage=0
    report_at=$(( now + REPORT_EVERY ))
  fi

  sleep "$TICK"
done
