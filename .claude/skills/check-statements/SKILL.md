---
name: check-statements
description: Guided session in which a person checks that Lean statements of Leanamics say what their source papers say, one item at a time, and records each check under their name in verification/checks/. Use when a contributor says they want to check statements, verify the translation of the papers into Lean, review statements against the sources, "do some statement checks", or names this skill; also when they ask which statements are still unchecked or want to check a specific result, package or kind of statement.
---

# Checking Lean statements against their sources

Lean checks the proofs of the library, but not that a Lean statement says what its source says,
and most statements and definitions were written by AI agents. In this skill **the person you are
talking to is the reviewer**: you show them one item at a time, the original statement next to the
Lean statement, answer their questions, and record a check only when they say so. The rules for
what a check means are in `verification/README.md`; read its sections "What a check means" and
"Original statements" once at the start.

All commands run from the repository root with `python3 scripts/check_statements.py` (Python
3.11+, standard library only; `$CS` below). They never change Lean files.

## The session, step by step

### 1. Start

1. Find the reviewer's name: `git config user.name`. Tell the user that checks will be recorded
   under that name (in `verification/checks/<name-slug>.jsonl`) and ask them to confirm or give
   another name. Use it as `--reviewer "NAME"` in every command.
2. Show the state in two lines: `$CS --report` gives the totals (items, checked by at least one
   and two reviewers); say how many items are checked and how many have an original statement
   transcribed.
3. If the user has not said what to check, offer the default (the next unchecked main result)
   and the alternatives in one short question: a package (`voter`, `moran`, `epidemics`,
   `undecided`, `averaging`, `median`, `plurality`, `crn`, `dynamics`), a topic (words matched
   with `--search`), definitions only, items they have not checked yet (second reviews), or
   one item by id or Lean name. Do not ask when they already said it.

### 2. Pick an item

- Default: `$CS --reviewer "NAME" --next` (the first item in priority order that nobody has
  checked; main results first, then the definitions they use).
- With a choice: add `--package P`, `--search "words"`, or `--filter unchecked-by-me` (items
  this reviewer has not checked, for a second review) or `--filter stale` (checks to redo
  after a statement changed). To see candidates, `--list` with the same options; for
  definitions, pick lines whose kind column is `def`.
- Items the user skips in this session: pass them all with `--skip ID ...` so `--next` moves on.

### 3. Show the item

Run `$CS --context ID` (Markdown: source, original statement and context, blueprint paraphrase,
Lean declarations with their variables, full text of the library definitions they use) and
`$CS --show ID` (adds the existing checks of the item, file paths and links). Present, in this
order:

1. **Header:** item id, the paper, the numbered result and the version, and the status of the
   transcription (for example "transcribed by an AI agent, not yet compared with the PDF by a
   person"). Give the paper link and page so the user can open it.
2. **Original statement**, verbatim, as LaTeX in a code block. Then its **context** (definitions,
   notation, model), verbatim. Do not paraphrase inside these blocks; if you add a readable
   rendering, label it as yours.
3. **Lean statement(s)**, verbatim in a `lean` code block, with the `variable` lines they use,
   then the definitions they use (verbatim, or the relevant ones if there are many; say which
   you left out).
4. **Reading aid**, labelled as your reading and not a check: a short table that pairs each
   hypothesis and the conclusion of the source with their Lean counterparts, and lists every
   visible difference (explicit constants instead of O(·) or "n large enough", extra or missing
   hypotheses, special cases, different conventions such as log base, sampling with or without
   replacement, rounds versus time). Point to the package's `FORMALIZATION_DIFFERENCES.md` when
   it discusses the item. Describe differences neutrally; do not call anything in the paper an
   error.

If the item has **no transcribed original statement**, say so plainly: the blueprint text is a
paraphrase written for the formalization, not the source. Give the reference and link, and
suggest that the user open the paper for this item (then the basis of the check is `paper`).

### 4. Questions

Let the user ask anything until they are convinced either way. Answer from the sources, not from
memory:
- Lean side: read the definitions in the `.lean` files (`--show` gives file and line), and if
  the user wants the elaborated statement, run `$CS --lean-type ID` (slow; needs the package
  built with `lake build` in that package).
- Paper side: the transcription, or the paper itself if the user wants (download the arXiv PDF
  or LaTeX source to a temporary directory outside the repository; never commit it).
- Small concrete examples help (what the statement says for n = 3, which value of a constant
  makes a hypothesis hold).

Say when you are unsure. Never push the user towards a verdict.

### 5. Ask for the verdict

Ask one question with these options:
- **agrees**: the Lean statement says what the source says, up to notation;
- **differs**: it says something else (intended or not); needs a comment saying what differs and
  whether it is intended (for example, "explicit constant 128 instead of a sufficiently large
  constant; intended");
- **unsure**: needs a comment with the open question; it is recorded but does not count as a
  check;
- **skip**: record nothing and move on.

Then the **basis**, unless the user already made it clear: `paper` (they compared with the paper
itself), `transcription` (with the original statement shown above, without opening the paper),
or `blueprint` (only the blueprint paraphrase; say that this is the weakest basis).

Only the user's explicit answer for this item counts. Never infer a verdict from the discussion,
never record one on your own judgment, and never record several items with one answer unless the
user explicitly asked for that and named the items. Draft the comment from the user's words and
show it to them before recording when you reworded it.

### 6. Record

```bash
$CS --reviewer "NAME" --record ID --verdict agrees|differs|unsure --basis paper|transcription|blueprint --comment "..."
```

Report the line it prints (`recorded: ...`). If it prints `nothing recorded`, fix the arguments
(for example, a missing comment) with the user. Never edit the `.jsonl` files by hand: a changed
verdict is a new check (the latest check of a reviewer counts).

Then go back to step 2 with the same choice, unless the user wants to stop or change it. Keep a
running count of the items checked in this session.

### 7. Finish

1. Summarize the session: items checked (with verdicts), skipped, and any `differs`/`unsure`
   comments.
2. Run `$CS --validate` (it must end with OK).
3. Show `git status --short verification/checks/`. The user's checks are in their own file, so
   their branch merges without conflicts with other reviewers' branches. Offer to commit the file
   (message such as "Statement checks: 5 items of voter") and open a pull request; do it only if
   they agree.

## What not to do

- Do not change Lean files, blueprints, `verification/sources*.toml` or other documentation during
  a check session. If the user finds a problem in a transcription or a statement, write it down
  and offer to open an issue (or a separate branch) after the session.
- Do not describe a check as anything more than the user's own comparison: "checked by NAME
  against the transcription" is not "verified against the paper".
- Do not run the checks of one reviewer under another reviewer's name.
