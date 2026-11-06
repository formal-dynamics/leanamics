#!/usr/bin/env python3
"""Recompute time, tool calls and tokens of the fixed-statement runs from the agents' own logs.

  run_metrics.py --grok-sessions DIR --vibe-sessions DIR [--json OUT] runs/*.json

The logs are not part of the repository. Each run config (`runs/<id>.json`) names the agent
sessions of the run in `logs.sessions`; the script looks them up by id:

* Grok command-line agent: DIR/<encoded working directory>/<session id>/, with `events.jsonl`
  (one timestamped event per line) and `usage.json` (token totals of the session).
* Mistral Vibe: DIR/session_<date>_<time>_<id prefix>/, with `meta.json` (start and end time,
  token statistics) and `messages.jsonl` (the conversation, without timestamps).

Measures, per run:

* time: for each session, from its first to its last logged event (Grok: first and last `ts` of
  `events.jsonl`; Vibe: `start_time` and `end_time` of `meta.json`); the run time is the sum
  over its sessions, so pauses between sessions are not counted. The span from the first event
  of the first session to the last event of the last one is reported too.
* tool calls: Grok: `tool_completed` events; Vibe: tool calls of the assistant messages, counted
  once per message id (a resumed session replays the earlier messages, which are not counted
  again).
* tokens: input (including cache reads) plus output tokens of every model call. Grok:
  `totalTokens` of `usage.json`, with `cachedReadTokens` for the cache-read share. Vibe:
  `session_total_llm_tokens` of `meta.json`; a session that continues another one after a context
  compaction (`parent_session_id` set) reports cumulative statistics, so its parent's are
  subtracted. Vibe does not record cache reads.
"""
import argparse
import glob
import json
import os
import sys
from datetime import datetime


def ts(s: str) -> datetime:
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def grok_session(root: str, sid: str) -> dict:
    hits = glob.glob(os.path.join(root, "*", sid))
    if len(hits) != 1:
        sys.exit(f"Grok session {sid}: found {len(hits)} directories")
    d = hits[0]
    stamps, tools = [], 0
    with open(os.path.join(d, "events.jsonl")) as f:
        for line in f:
            e = json.loads(line)
            stamps.append(ts(e["ts"]))
            tools += e["type"] == "tool_completed"
    usage = json.load(open(os.path.join(d, "usage.json")))["session"]
    return {"id": sid, "start": min(stamps), "end": max(stamps), "tool_calls": tools,
            "tokens": usage["totalTokens"], "cache_read": usage["cachedReadTokens"],
            "model_calls": usage["modelCalls"], "parent": None}


def vibe_session(root: str, sid: str) -> dict:
    hits = [d for d in glob.glob(os.path.join(root, f"session_*_{sid[:8]}"))
            if json.load(open(os.path.join(d, "meta.json")))["session_id"] == sid]
    if len(hits) != 1:
        sys.exit(f"Vibe session {sid}: found {len(hits)} directories")
    d = hits[0]
    meta = json.load(open(os.path.join(d, "meta.json")))
    msgs = [json.loads(l) for l in open(os.path.join(d, "messages.jsonl"))]
    st = meta["stats"]
    return {"id": sid, "start": ts(meta["start_time"]), "end": ts(meta["end_time"]),
            "messages": msgs, "tokens_cum": st["session_total_llm_tokens"], "steps_cum": st["steps"],
            "cache_read": None, "parent": meta.get("parent_session_id")}


def tool_calls_of(msg: dict) -> int:
    tc = msg.get("tool_calls") or []
    if isinstance(tc, str):  # stored as a Python literal in some versions
        import ast
        tc = ast.literal_eval(tc)
    return len(tc)


def run_metrics(cfg: dict, grok_root: str, vibe_root: str) -> dict:
    kind, ids = cfg["logs"]["kind"], cfg["logs"]["sessions"]
    if kind == "grok":
        sessions = [grok_session(grok_root, s) for s in ids]
    else:
        sessions = [vibe_session(vibe_root, s) for s in ids]
        by_id = {s["id"]: s for s in sessions}
        seen = set()
        for s in sessions:
            new = [m for m in s["messages"] if m.get("message_id") not in seen]
            seen.update(m.get("message_id") for m in s["messages"])
            s["tool_calls"] = sum(tool_calls_of(m) for m in new if m.get("role") == "assistant")
            p = by_id.get(s["parent"])
            s["tokens"] = s["tokens_cum"] - (p["tokens_cum"] if p else 0)
            s["model_calls"] = s["steps_cum"] - (p["steps_cum"] if p else 0)
    rows = []
    for s in sessions:
        rows.append({"session": s["id"], "start": s["start"].isoformat(), "end": s["end"].isoformat(),
                     "seconds": round((s["end"] - s["start"]).total_seconds(), 1),
                     "tool_calls": s["tool_calls"], "tokens": s["tokens"], "model_calls": s["model_calls"],
                     "cache_read": s["cache_read"], "continues": s["parent"]})
    secs = sum(r["seconds"] for r in rows)
    span = (max(s["end"] for s in sessions) - min(s["start"] for s in sessions)).total_seconds()
    tokens = sum(r["tokens"] for r in rows)
    cache = None if kind == "vibe" else sum(r["cache_read"] for r in rows)
    return {"id": cfg["id"], "target": cfg["target"], "agent": cfg["agent"], "sessions": rows,
            "seconds": round(secs, 1), "span_seconds": round(span, 1),
            "tool_calls": sum(r["tool_calls"] for r in rows), "tokens": tokens,
            "model_calls": sum(r["model_calls"] for r in rows),
            "cache_read_share": None if cache is None else round(cache / tokens, 4)}


def mmss(sec: float) -> str:
    sec = round(sec)
    return f"{sec // 60}:{sec % 60:02d}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("configs", nargs="+")
    ap.add_argument("--grok-sessions", required=True)
    ap.add_argument("--vibe-sessions", required=True)
    ap.add_argument("--json", help="also write the full results here")
    a = ap.parse_args()
    results = [run_metrics(json.load(open(c)), a.grok_sessions, a.vibe_sessions) for c in a.configs]
    print("| Run | Sessions | Time (m:s) | Time (min) | Span (m:s) | Tool calls | Model calls "
          "| Tokens | Cache reads |")
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for r in results:
        share = "n/a" if r["cache_read_share"] is None else f"{100 * r['cache_read_share']:.1f}%"
        print(f"| {r['id']} | {len(r['sessions'])} | {mmss(r['seconds'])} | {round(r['seconds'] / 60)} "
              f"| {mmss(r['span_seconds'])} | {r['tool_calls']} | {r['model_calls']} "
              f"| {r['tokens']:,} ({r['tokens'] / 1e6:.1f}M) | {share} |")
    multi = [r for r in results if len(r["sessions"]) > 1]
    if multi:
        print("\nRuns with several sessions (start time in UTC):\n\n```")
    for r in multi:
        print(f"{r['id']}:")
        for s in r["sessions"]:
            cont = f", continues {s['continues'][:8]} after a context compaction" if s["continues"] else ""
            print(f"  {s['session'][:8]}  {s['start'][:19]}Z  {mmss(s['seconds']):>6}  "
                  f"{s['tool_calls']:4d} tool calls  {s['tokens']:>11,} tokens{cont}")
    if multi:
        print("```")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(results, f, indent=1)
            f.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
