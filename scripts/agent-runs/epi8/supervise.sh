#!/usr/bin/env bash
# Unattended Grok supervisor for EPI-8: run, gate, resume with a status prompt; stop when done,
# when the Grok pool is exhausted, after MAX_ROUNDS, or after the DEADLINE (epoch seconds).
set -u
RUN=${RUN:-$HOME/repos/epi8-run}
WT=${WT:?worktree}
MAX_ROUNDS=${MAX_ROUNDS:-6}
DEADLINE=${DEADLINE:?epoch}
# grok's install location differs between machines (e.g. ~/.grok/bin or ~/.local/bin)
GROK=${GROK:-$(command -v grok || ls "$HOME"/.grok/bin/grok "$HOME"/.local/bin/grok 2>/dev/null | head -1)}
[ -x "$GROK" ] || { echo "grok binary not found" >&2; exit 1; }
log() { echo "[$(date '+%F %T')] $*" >> "$RUN/supervise.log"; }

gate() {  # writes $RUN/gate.txt, returns 0 iff accepted
  {
    echo "== spec gate"; python3 "$RUN/check_spec.py" check "$WT" "$RUN/baseline.json"; s=$?
    echo "== lake build"
    (cd "$WT/epidemics" && timeout 3600 lake build Epidemics 2>&1 | grep -v '^✔' | tail -80); b=${PIPESTATUS[0]}
    w=$(cd "$WT/epidemics" && lake build Epidemics 2>&1 | grep -c -E '^(warning|error)')
    echo "== build exit $b, warning/error lines $w"
    [ $s -eq 0 ] && [ $b -eq 0 ] && [ "$w" -eq 0 ]
  } > "$RUN/gate.txt" 2>&1
}

SID=""
for round in $(seq 1 "$MAX_ROUNDS"); do
  now=$(date +%s); if [ "$now" -ge "$DEADLINE" ]; then log "deadline reached, stop"; break; fi
  budget=$(( DEADLINE - now ))
  out="$RUN/run$round.jsonl"; err="$RUN/run$round.err"
  if [ -z "$SID" ]; then
    log "round $round: fresh session"
    ( cd "$WT" && timeout "$budget" "$GROK" --prompt-file "$RUN/task.md" --cwd "$WT" --sandbox workspace --yolo \
        --effort high --max-turns 500 --output-format streaming-json </dev/null > "$out" 2> "$err" )
  else
    log "round $round: resume $SID"
    ( cd "$WT" && timeout "$budget" "$GROK" --resume "$SID" --prompt-file "$RUN/next.md" --cwd "$WT" --sandbox workspace \
        --yolo --effort high --max-turns 300 --output-format streaming-json </dev/null > "$out" 2> "$err" )
  fi
  log "round $round exited $?"
  s=$(grep '"type":"end"' "$out" | tail -1 | python3 -c 'import sys,json
l=sys.stdin.read().strip()
print(json.loads(l).get("sessionId","") if l else "")' 2>/dev/null)
  [ -n "$s" ] && SID=$s
  if [ -z "$SID" ]; then  # fall back to the newest session dir for this cwd
    enc=$(python3 -c 'import sys,urllib.parse;print(urllib.parse.quote(sys.argv[1],safe=""))' "$WT")
    SID=$(ls -t "$HOME/.grok/sessions/$enc" 2>/dev/null | head -1)
  fi
  log "session $SID; end: $(grep '"type":"end"' "$out" | tail -1 | cut -c1-300)"
  if grep -q -E '402|usage balance exhausted' "$err" "$out"; then log "Grok pool exhausted, stop"; break; fi
  if gate; then log "ACCEPTED by gate (SPEC OK, clean build)"; touch "$RUN/DONE"; break; fi
  log "gate failed: $(grep -E 'FAIL|exit' "$RUN/gate.txt" | head -5 | tr '\n' ' ')"
  { echo "Status check by the supervisor: the task is not finished yet. Continue with the same task"
    echo "(the original instructions and protocol still hold; re-read PROGRESS.md and task.md is in your"
    echo "context). Here is the current output of the spec gate and of 'lake build Epidemics':"
    echo; echo '```'; cat "$RUN/gate.txt"; echo '```'
    echo; echo "Fix the remaining errors and sorries, keep PROGRESS.md up to date, and stop when the build is"
    echo "clean and warning-free with no sorry left." ; } > "$RUN/next.md"
done
log "supervisor finished"
