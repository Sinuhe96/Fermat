#!/bin/sh
# =====================================================================
# mem_watch.sh — resource sampler for the M1 lane (slow-round forensics).
#
# Companion to watch_lane.sh. It judges nothing and latches nothing: it
# appends one MEM line per tick to pipeline/03-lean/M1_mem.log so the
# next slow round carries its own cause instead of being unrecoverable
# (rounds 1-16 of M1_rounds.tsv ran 300-371s with no resource record).
#
# MEM line fields (tab-separated after the timestamp):
#   proc=<lakes>/<leans>   in-container compile processes (same count as
#                          watch_lane.sh, for alignment with HB lines)
#   cur=  memory.current   cgroup working set now (bytes)
#   peak= memory.peak      cgroup high-water mark; == mem_limit means the
#                          container hit its cap (direct reclaim at work)
#   swap= memory.swap.current
#   maxev= memory.events "max" counter — delta across a round = how often
#        the cgroup hit the cap (millions = sustained reclaim pressure)
#   oom=  memory.events oom counter — any OOM kill is a hard finding
#   psi=  memory.pressure "some avg10" — kernel memory-pressure stall time
#   host=<free>/<total>    host physical memory (GiB), Windows side
#
# The container sample reads /proc and /sys only (no lean/lake spawned),
# so this service never trips watch_lane.sh's CONTENTION latch.
#
# Env: ROOT (repo root), TICK (seconds, default 60).
# Keep TICK equal to watch_lane.sh's so MEM and HB lines interleave 1:1.
# =====================================================================
set -u

ROOT="${ROOT:-$(pwd)}"
cd "$ROOT" || exit 1
OUT="$ROOT/pipeline/03-lean/M1_mem.log"
TICK="${TICK:-60}"

mkdir -p "$(dirname "$OUT")"

log() { printf '%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$1" >> "$OUT"; }

printf 'MEMWATCH-READY tick=%ss root=%s out=%s\n' "$TICK" "$ROOT" "$OUT"
log "MEMWATCH-START	tick=$TICK"

while :; do
  # One exec per tick: process counts + cgroup counters, single sh call.
  inc=$(docker compose exec -T lean sh -c '
    l=0; n=0
    for c in /proc/[0-9]*/comm; do t=$(cat "$c" 2>/dev/null); case "$t" in lake) l=$((l+1));; lean) n=$((n+1));; esac; done
    g=/sys/fs/cgroup
    cur=$(cat "$g/memory.current" 2>/dev/null || echo 0)
    peak=$(cat "$g/memory.peak" 2>/dev/null || echo 0)
    sw=$(cat "$g/memory.swap.current" 2>/dev/null || echo 0)
    mx=$(sed -n "s/^max //p" "$g/memory.events" 2>/dev/null)
    om=$(sed -n "s/^oom //p" "$g/memory.events" 2>/dev/null)
    psi=$(sed -n "s/^some \(avg10=[^ ]*\).*/\1/p" "$g/memory.pressure" 2>/dev/null)
    echo "proc=$l/$n cur=$cur peak=$peak swap=$sw maxev=${mx:-?} oom=${om:-?} psi=${psi:-NA}"' \
    2>/dev/null | tr -d '\r' | tail -n 1)

  # Host physical memory, GiB free/total. PowerShell costs ~0.5-1s per
  # tick; guarded so an unavailable PowerShell degrades to NA.
  host=$(powershell -NoProfile -Command \
    '$o=Get-CimInstance Win32_OperatingSystem; "{0}/{1}" -f [int]($o.FreePhysicalMemory/1048576), [int]($o.TotalVisibleMemorySize/1048576)' \
    2>/dev/null | tr -d '\r' | tail -n 1)
  case "$host" in
    ''|*[!0-9/]*) host=NA/NA ;;
  esac

  log "MEM	${inc:-down}	host=${host}"
  printf 'MEM %s %s host=%s\n' "$(date -u +%H:%M:%SZ)" "${inc:-down}" "$host"

  sleep "$TICK"
done
