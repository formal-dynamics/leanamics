# Checking statements against their sources

Lean checks the proofs of the library, but not whether a Lean statement says what the source
paper says, and most statements and definitions of the library were written by AI agents. This
directory records which statements people have compared with their sources. The record is
read by `scripts/check_statements.py` (Python 3.11+, standard library only).

The easiest way to check statements is the Claude Code skill `check-statements`
(`.claude/skills/check-statements/`): say that you want to check statements, and it picks the next
unchecked item (or one of the kind you ask for), shows the original statement next to the Lean
statement, answers your questions, and records your verdict when you give it. The same steps by
hand:

```bash
python3 scripts/check_statements.py --next                     # the next unchecked item
python3 scripts/check_statements.py --next --package voter     # ... of one package
python3 scripts/check_statements.py --show voter:thm:21        # one item, as plain text
python3 scripts/check_statements.py --context voter:thm:21     # as Markdown, with the definitions used
python3 scripts/check_statements.py --record voter:thm:21 --verdict agrees --basis transcription
python3 scripts/check_statements.py --record voter:thm:21 --verdict differs --basis paper \
    --comment "explicit constant 128 instead of a large enough constant; intended"
python3 scripts/check_statements.py --list --filter unchecked  # all unchecked items
python3 scripts/check_statements.py --report                   # Markdown summary
python3 scripts/check_statements.py --validate                 # for CI; non-zero exit on error
```

Your name comes from `git config user.name` (or `--reviewer "Ada Lovelace"`).

## Items

An item is a node of a package blueprint (`<package>/blueprint/src/content.tex`) that names Lean
declarations with `\lean{...}`: a definition, theorem, lemma, corollary or proposition. Its id
is `<package>:<label>`, for example `plurality:thm:3_8`. For each item `--show` and `--context` give:

- the source: the entry of `sources.toml` (paper, version, numbered result, page and the
  original statement, when transcribed), the rows of `PROVENANCE.md` and of the package README
  that cite its declarations, the blueprint section, and arXiv/DOI links;
- the blueprint statement (a paraphrase written for the formalization, not the source);
- each Lean declaration: doc comment, file and line, the section `variable`s the statement uses,
  and the statement (the signature up to `:=` for a theorem; the whole text for a definition,
  structure or inductive type);
- the library definitions the statement uses, with the items that name them.

The list puts first the main results (those with an entry in `sources.toml` or that open a row of
the result tables of `PROVENANCE.md`, outside the shared layer), then the items whose
definitions these results use, then the other results cited in `PROVENANCE.md`, the other
definitions, and the rest.

## What a check means

A check of an item by a reviewer says: *I read the Lean statements of this item (with the
variables and the definitions they use) and compared them with the source.* The source is the
original statement of the numbered result in the paper (or its transcription in `sources.toml`,
which you should compare with the PDF when it says "not yet compared"); for an item without a
numbered source result, such as most definitions and auxiliary lemmas, it is the mathematical
object or claim that the blueprint attributes to the paper. The verdict is one of:

- `agrees`: the Lean statement says what the source says, up to notation. A definition agrees
  when it defines the object the paper means.
- `differs`: the Lean statement says something else. The comment is mandatory: say what differs
  and whether the difference is intended (explicit constants instead of "sufficiently large",
  a correction listed in the package's `FORMALIZATION_DIFFERENCES.md`, a weaker or stronger
  hypothesis, a special case). An intended difference is still a check.
- `unsure`: you could not decide. The comment is your question. It does not count as a check.

A check is about the statement only, not the proof (Lean checks the proof), and only about the
declarations the item names. A theorem can be meaningless if a definition it uses is wrong: check
the definitions too (they are items of their own when the blueprint names them; `--report`
counts the library definitions used by statements that no item names). The answers of the `A`
Answers of an assistant are not checks: a check is recorded only by
`--record`, run by the reviewer or, in the skill, on the reviewer's explicit answer for that item.

Each check also records its **basis**, what the Lean statement was compared with:

- `paper`: the paper itself (PDF or printed copy);
- `transcription`: the original statement and context in the sources files, without opening the
  paper (the transcriptions were made by AI agents; see below);
- `blueprint`: only the blueprint paraphrase, which was written for the formalization and is not
  the source. This is the weakest basis.

`--report` counts the current checks by basis.

## How checks are stored

Every check is one line of JSON appended to `verification/checks/<reviewer>.jsonl`, where
`<reviewer>` is the reviewer's name in lower case ASCII (`Niccolò D'Archivio` writes to
`niccolo-d-archivio.jsonl`):

```json
{"item": "voter:thm:21", "reviewer": "Ada Lovelace", "date": "2026-11-04T17:00:00Z",
 "verdict": "agrees", "comment": "", "lean_hash": "43d55325c5511826",
 "source_hash": "8b8af7c78d0fb0d8", "lean": ["Voter.eventualColor", "..."], "version": 1}
```

Lines are never edited or deleted. To change your verdict, record a new check: the latest check
of each reviewer counts. Commit your file like any other change. Since every reviewer appends to
their own file, four people can check items on four branches and the branches merge without
conflicts; `.gitattributes` also sets `merge=union` on these files for the case of one reviewer
working on two branches. `--validate` checks that every line is well formed, that every item id
exists and that every `\lean{}` name of the blueprints is declared in the Lean sources.

## Stale checks

With each check the checker records two hashes: of the Lean text of the item (the statements of its
declarations as described above, without comments, whitespace collapsed, with the section
variables they use) and of its source text (the blueprint title and statement, and the version,
numbered result, statement and context of its `sources.toml` entries). When either changes, the
earlier checks of the item become stale: they are marked as such, they no longer count, and the item
must be checked again. A new proof, doc comment or comment does not make a check stale; a
changed hypothesis, conclusion or definition body does. The hashes cover the declarations the
item names, not the definitions they use, which are checked as their own items.

## Counting

For the paper, an item is *checked by* a reviewer when that reviewer's latest check of it is
current (not stale) and its verdict is `agrees` or `differs`. `--report` prints, per package, the
number of items checked by at least one and by at least two reviewers, the stale checks, the
recorded differences with their comments and the open questions, and the number of items by
number of reviewers.

## Original statements: `sources.toml` and `sources/`

`sources.toml` and the per-package files `sources/<package>.toml` (same format; separate files so
that several people can transcribe in parallel) give, per item, the source reference (paper, version, numbered result, page)
and, when available, the original statement transcribed from the source, with the definitions it
depends on (`context`). The header of `sources.toml` describes the fields.

All entries were made by AI agents, from the arXiv LaTeX sources or from open copies of the
papers (author pages, open archives, open-access proceedings), and their `status` says exactly
what was done, for example "transcribed from the arXiv LaTeX source of v2 and compared with the
PDF of v2; not yet checked by a person". When no open copy was found (some books, and papers such
as Hassin and Peleg 2001 or Coppersmith, Tetali and Winkler 1993), the entry gives the reference
only, without `statement`, and its status says so: compare those items with the paper itself
(basis `paper`). Items that are lemmas of the formalization, with no counterpart in a source, have
no entry. When you compare an entry with the paper, change its `status` (for example to "compared
with the PDF of arXiv v2 by Ada Lovelace, 2026-11-10"); the status is not part of the hash, so
this does not make checks stale.

## Asking Lean

`--lean-type ID` runs `lake env lean` on a temporary file with `#check @name` for the item's
declarations and prints the elaborated types. It needs the package to be built and takes a minute
or two. It cross-checks the text extraction (for example, which section variables a statement
uses); the other commands do not depend on it.

## Limitations

The declarations are extracted from the text of the `.lean` files, not by Lean. The extraction
relies on the conventions of the library (commands start in column 0, namespaces are closed by
`end`), and the tests check that every `\lean{}` name of the blueprints is found. The definitions
"used by the statement" are the identifiers of the statement that resolve to declarations of the
library under the namespaces and `open`s in force; generalized field notation (`H.Stationary`) is
resolved only when the field name is unique in the library, so the list can miss a definition.
Mathlib declarations are not listed.
