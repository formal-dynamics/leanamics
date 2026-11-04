# Checking statements against their sources

Lean checks the proofs of the library, but not whether a Lean statement says what the source
paper says, and most statements and definitions of the library were written by AI agents. This
directory records which statements people have compared with their sources. The record is
read by `scripts/check_statements.py`, a terminal app (Python 3.11+ standard library only):

```bash
python3 scripts/check_statements.py                    # the app; your name from git config user.name
python3 scripts/check_statements.py --reviewer "Ada Lovelace"
python3 scripts/check_statements.py --report           # Markdown summary
python3 scripts/check_statements.py --validate         # for CI; non-zero exit on error
python3 scripts/check_statements.py --list --filter unchecked
python3 scripts/check_statements.py --show voter:thm:21   # one item, as plain text
```

Press `?` in the app for the keys.

## Items

An item is a node of a package blueprint (`<package>/blueprint/src/content.tex`) that names Lean
declarations with `\lean{...}`: a definition, theorem, lemma, corollary or proposition. Its id
is `<package>:<label>`, for example `plurality:thm:3_8`. For each item the app shows:

- the source: the entry of `sources.toml` (paper, version, numbered result, page and the
  original statement, when transcribed), the rows of `PROVENANCE.md` and of the package README
  that cite its declarations, the blueprint section, and arXiv/DOI links;
- the blueprint statement (a paraphrase written for the formalization, not the source);
- each Lean declaration: doc comment, file and line, the section `variable`s the statement uses,
  and the statement (the signature up to `:=` for a theorem; the whole text for a definition,
  structure or inductive type);
- the library definitions the statement uses, with the items that name them (press `D`).

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
key (see below) are not checks, and nothing records a check except a reviewer pressing `a`, `d`
or `u` in the app.

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

With each check the app records two hashes: of the Lean text of the item (the statements of its
declarations as described above, without comments, whitespace collapsed, with the section
variables they use) and of its source text (the blueprint title and statement, and the version,
numbered result, statement and context of its `sources.toml` entries). When either changes, the
earlier checks of the item become stale: the app marks them, they no longer count, and the item
must be checked again. A new proof, doc comment or comment does not make a check stale; a
changed hypothesis, conclusion or definition body does. The hashes cover the declarations the
item names, not the definitions they use, which are checked as their own items.

## Counting

For the paper, an item is *checked by* a reviewer when that reviewer's latest check of it is
current (not stale) and its verdict is `agrees` or `differs`. `--report` prints, per package, the
number of items checked by at least one and by at least two reviewers, the stale checks, the
recorded differences with their comments and the open questions, and the number of items by
number of reviewers.

## Original statements: `sources.toml`

`sources.toml` gives, per item, the source reference (paper, version, numbered result, page)
and, when available, the original statement transcribed from the source, with the definitions it
depends on (`context`). The header of the file describes the fields. The first entries cover the
headline results that `PROVENANCE.md` lists from papers on arXiv; they were transcribed by an AI
agent from the arXiv LaTeX sources (statements only) and are marked "transcribed from the arXiv
LaTeX source, not yet compared with the PDF". When you compare one with the PDF, change its
`status` (for example to "compared with the PDF of arXiv v2 by Ada Lovelace, 2026-11-10"); the
status is not part of the hash, so this does not make checks stale. Papers that are not on arXiv
(Hassin and Peleg 2001; Doerr et al., SPAA 2011; the OPODIS 2016 exact-majority paper; the
classical results) have no entry yet.

## Asking an assistant

The `A` key sends the item (source, blueprint statement, Lean statements and the definitions they
use, as Markdown, with your question) on standard input to the shell command in the environment
variable `CHECK_STATEMENTS_ASK_CMD`, run in the repository root, and shows its standard output.
No vendor is built in: any command that reads a prompt on standard input works. Without the
variable, the context is written to a temporary file and the app says where.
`--ask-context ID` prints the same context.

## Asking Lean

The `L` key (or `--lean-type ID`) runs `lake env lean` on a temporary file with `#check @name` for
the item's declarations and shows the elaborated types. It needs the package to be built and
takes a minute or two. It cross-checks the text extraction (for example, which section variables
a statement uses); the rest of the app does not depend on it.

## Limitations

The declarations are extracted from the text of the `.lean` files, not by Lean. The extraction
relies on the conventions of the library (commands start in column 0, namespaces are closed by
`end`), and the tests check that every `\lean{}` name of the blueprints is found. The definitions
"used by the statement" are the identifiers of the statement that resolve to declarations of the
library under the namespaces and `open`s in force; generalized field notation (`H.Stationary`) is
resolved only when the field name is unique in the library, so the list can miss a definition.
Mathlib declarations are not listed.
