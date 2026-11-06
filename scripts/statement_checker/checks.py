"""The record of checks: append-only JSON Lines files, one per reviewer.

Every line of `verification/checks/<reviewer-slug>.jsonl` is one check:

    {"item": "voter:thm:21", "reviewer": "Ada Lovelace", "date": "2026-11-04T17:00:00Z",
     "verdict": "agrees", "comment": "", "lean_hash": "...", "source_hash": "...",
     "lean": ["Voter.consensus_probability", ...], "version": 1}

Lines are never edited or removed: a reviewer who changes their mind records a new check, and
the latest check of each reviewer counts. A reviewer appends only to their own file, so checks
made on different branches merge without conflicts (`.gitattributes` also sets `merge=union`
on these files, for the case of one reviewer working on two branches).

The optional field `basis` says what the reviewer compared the Lean statement with: `paper`
(the paper itself, PDF or printed copy), `transcription` (the original statement transcribed in
the sources files, without opening the paper) or `blueprint` (only the blueprint paraphrase,
which was written for the formalization and is not the source).

A check is stale when the hash of the item's Lean text or of its source text differs from the
hash recorded with it: the statement was changed after the check.
"""
import datetime
import hashlib
import json
import re
import unicodedata
from dataclasses import dataclass
from pathlib import Path

VERDICTS = ("agrees", "differs", "unsure")
BASES = ("paper", "transcription", "blueprint")
NEEDS_COMMENT = ("differs", "unsure")
FIELDS = ("item", "reviewer", "date", "verdict", "comment", "lean_hash", "source_hash")
VERSION = 1
HASH_LEN = 16


def digest(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:HASH_LEN]


def slug(name):
    """A file name for a reviewer: ASCII, lower case, words joined by `-`."""
    s = unicodedata.normalize("NFKD", name).encode("ascii", "ignore").decode()
    s = re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")
    return s or "reviewer"


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


@dataclass
class Check:
    item: str
    reviewer: str
    date: str
    verdict: str
    comment: str
    lean_hash: str
    source_hash: str
    lean: tuple = ()
    basis: str = ""
    file: str = ""
    line: int = 0

    def to_json(self):
        obj = {"item": self.item, "reviewer": self.reviewer, "date": self.date,
               "verdict": self.verdict, "comment": self.comment, "lean_hash": self.lean_hash,
               "source_hash": self.source_hash, "lean": list(self.lean)}
        if self.basis:
            obj["basis"] = self.basis
        obj["version"] = VERSION
        return json.dumps(obj, ensure_ascii=False, sort_keys=False)


def validate_record(obj):
    """Problems of one decoded line (empty list if it is well formed)."""
    if not isinstance(obj, dict):
        return ["not a JSON object"]
    problems = []
    for f in FIELDS:
        if f not in obj:
            problems.append(f"missing field `{f}`")
        elif not isinstance(obj[f], str):
            problems.append(f"field `{f}` is not a string")
    if problems:
        return problems
    if obj["verdict"] not in VERDICTS:
        problems.append(f"verdict `{obj['verdict']}` is not one of {', '.join(VERDICTS)}")
    if obj["verdict"] in NEEDS_COMMENT and not obj["comment"].strip():
        problems.append(f"verdict `{obj['verdict']}` needs a comment")
    if not obj["reviewer"].strip():
        problems.append("empty reviewer")
    try:
        datetime.datetime.strptime(obj["date"], "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        problems.append(f"date `{obj['date']}` is not YYYY-MM-DDTHH:MM:SSZ (UTC)")
    for f in ("lean_hash", "source_hash"):
        if not re.fullmatch(r"[0-9a-f]{%d}" % HASH_LEN, obj[f]):
            problems.append(f"`{f}` is not {HASH_LEN} hex digits")
    if "lean" in obj and not (isinstance(obj["lean"], list)
                              and all(isinstance(x, str) for x in obj["lean"])):
        problems.append("`lean` is not a list of names")
    if "basis" in obj and obj["basis"] not in BASES:
        problems.append(f"basis `{obj['basis']}` is not one of {', '.join(BASES)}")
    return problems


class Store:
    """All checks of a directory of `.jsonl` files."""

    def __init__(self, directory):
        self.dir = Path(directory)
        self.checks = []
        self.problems = []   # (file, line, message)
        self.load()

    def load(self):
        self.checks, self.problems = [], []
        if not self.dir.is_dir():
            return
        for path in sorted(self.dir.glob("*.jsonl")):
            for k, raw in enumerate(path.read_text(encoding="utf-8").split("\n")):
                if not raw.strip():
                    continue
                try:
                    obj = json.loads(raw)
                except json.JSONDecodeError as e:
                    self.problems.append((path.name, k + 1, f"invalid JSON: {e}"))
                    continue
                probs = validate_record(obj)
                if probs:
                    self.problems += [(path.name, k + 1, p) for p in probs]
                    continue
                self.checks.append(Check(
                    item=obj["item"], reviewer=obj["reviewer"].strip(), date=obj["date"],
                    verdict=obj["verdict"], comment=obj["comment"],
                    lean_hash=obj["lean_hash"], source_hash=obj["source_hash"],
                    lean=tuple(obj.get("lean", ())), basis=obj.get("basis", ""),
                    file=path.name, line=k + 1))

    def path_for(self, reviewer):
        return self.dir / f"{slug(reviewer)}.jsonl"

    def append(self, check):
        """Append a check to its reviewer's file and to the in-memory list."""
        probs = validate_record(json.loads(check.to_json()))
        if probs:
            raise ValueError("; ".join(probs))
        self.dir.mkdir(parents=True, exist_ok=True)
        path = self.path_for(check.reviewer)
        line = check.to_json() + "\n"
        prefix = ""
        if path.is_file():
            data = path.read_bytes()
            if data and not data.endswith(b"\n"):
                prefix = "\n"
        with open(path, "a", encoding="utf-8") as f:
            f.write(prefix + line)
        check.file = path.name
        self.checks.append(check)

    def for_item(self, item_id):
        return [c for c in self.checks if c.item == item_id]


def latest_by_reviewer(checks):
    """The latest check of each reviewer (by date, then by order in the files)."""
    out = {}
    for c in checks:
        prev = out.get(c.reviewer)
        if prev is None or c.date >= prev.date:
            out[c.reviewer] = c
    return out


def is_stale(check, lean_hash, source_hash):
    return check.lean_hash != lean_hash or check.source_hash != source_hash


def stale_parts(check, lean_hash, source_hash):
    parts = []
    if check.lean_hash != lean_hash:
        parts.append("Lean")
    if check.source_hash != source_hash:
        parts.append("source")
    return parts


@dataclass
class Status:
    """The check status of one item."""
    checked_by: tuple = ()     # reviewers whose latest check is current, agrees or differs
    agrees: tuple = ()
    differs: tuple = ()
    unsure: tuple = ()
    stale: tuple = ()          # reviewers whose latest check is stale
    mine: object = None        # the latest check of the current reviewer, or None
    mine_stale: bool = False

    @property
    def n(self):
        return len(self.checked_by)


def status(checks, lean_hash, source_hash, me=None):
    latest = latest_by_reviewer(checks)
    agrees, differs, unsure, stale = [], [], [], []
    for r, c in sorted(latest.items()):
        if is_stale(c, lean_hash, source_hash):
            stale.append(r)
        elif c.verdict == "agrees":
            agrees.append(r)
        elif c.verdict == "differs":
            differs.append(r)
        else:
            unsure.append(r)
    mine = latest.get(me) if me else None
    return Status(checked_by=tuple(agrees + differs), agrees=tuple(agrees),
                  differs=tuple(differs), unsure=tuple(unsure), stale=tuple(stale), mine=mine,
                  mine_stale=bool(mine and is_stale(mine, lean_hash, source_hash)))
