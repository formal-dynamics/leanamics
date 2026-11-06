# Fixed-statement agent runs

Eight results of the library were proved by LLM agents under a fixed-statement protocol: the
definitions and theorem statements were written and committed first, with `sorry` proofs, and an
agent then had to replace every `sorry` without changing any statement. Acceptance was decided by
a mechanical check, not by the agent's report (in two runs, after the review of one flagged line).
This directory publishes that check and the data of the eight runs:

| File | Content |
| --- | --- |
| `check_spec.py` | the acceptance check (one script for all runs) |
| `runs/<run>.json` | per run: pinned and accepted commits, pinned file and declarations, allowed files, check parameters, agent sessions |
| `prompts/` | the prompts given to the agents, verbatim |
| `run_metrics.py` | recomputes time, tool calls and tokens from the agents' session logs |
| `metrics.md`, `metrics.json` | its output for the eight runs |

## Protocol

1. The definitions and statements of a target are written in Lean with `sorry` proofs and committed
   once they compile. This is the *pinned* commit.
2. The agent gets a prompt (in `prompts/`) with the rules, the commands to build and audit, and an
   informal proof plan. It works in a separate git worktree at the pinned commit, with the
   dependencies already built, under a sandbox that confines its writes to that worktree. The
   prompt forbids git commands that write.
3. After the run, the acceptance check is run from outside the worktree. The agent's files are then
   committed as the *accepted* commit, a child of the pinned commit (for `two-choices`, a child of
   a commit of the partial proof, see below).

The six runs with the Grok command-line agent (model grok-4.7) each ran in one session and ended
on their own. The two runs with GLM-5.3, driven by the Mistral Vibe agent, ran in several sessions:
a session that ended on a tool call written as plain text, on a server error, or without a final
reply was followed by a new one, which continued from the files and the agent's progress notes.

## What the check verifies

`check_spec.py RUN.json` compares a checkout (or, with `--rev`, a commit) with the pinned commit
named in `RUN.json`, and reports every violation. The docstring of the script gives the exact rules.

Checks that the per-run scripts used during the runs performed:

1. **Statements.** Each pinned definition is byte-identical to the baseline, from its keyword line
   to the first blank line. Each pinned theorem is byte-identical from its keyword line up to its
   first `:=`. In the four later runs (undecided, averaging, and both median runs) the `variable`,
   `namespace` and `open` lines of the pinned file must also be unchanged (in the median runs, the
   `import` lines too), because such a line can change what the names in a statement refer to. In
   the median runs, the definitions live in `median/Median/Defs.lean`, which the agent may not
   change.
2. **Banned tokens.** No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `axiom`
   declarations, `debug.skipKernelTC` or `Kernel.skip` in the code of the scanned files.
3. **Files.** Every file changed since the pinned commit, tracked or not, matches the run's
   `allowed` pattern.

The eight per-run scripts were copies of one script that differed only in the parameters now
stored in `runs/<run>.json`: the pinned file and declarations, the declaration keywords, the
pinned context lines, the allowed files and the scanned files. With these parameters
`check_spec.py` performs the same checks. The baseline is read from the pinned commit with
`git show`, and for all eight runs it is identical to the snapshot the per-run script had recorded.

One parameter differs from the scripts of the time: the two median runs ran in parallel in the
same package, so each accepted commit still contains the `sorry`s of the other run's pinned file.
For them the scan covers the run's own files (`median/Median/Basic*.lean`,
`median/Median/Binary*.lean`), as the commit messages of the two accepted commits record. Since
the agent may change no other file, a banned token elsewhere can only come from the pinned commit.

Checks that `check_spec.py` adds. They were not part of the per-run scripts: the build and the
axiom audit were separate steps (the prompts give the commands), and the last three are new.

4. **Build** (`--build`): `lake build` succeeds in the package, with no warning in a file the
   agent changed.
5. **Axioms** (`--axioms`): every pinned theorem depends only on `propext`, `Classical.choice`
   and `Quot.sound`.
6. **The `omit` rule** (always on): the command modifiers directly above a pinned theorem (lines
   ending in ` in`, attributes) are those of the baseline, except that `omit … in` lines and
   `set_option maxHeartbeats … in` (or `maxRecDepth`, `synthInstance.maxHeartbeats`) lines may be
   added. Before, a line such as `include h in` above a theorem would not have been detected.
7. **Context lines for all runs** (`--strict`): pins the `variable`, `namespace`, `open` and
   `include` lines also in the four early runs, whose scripts did not pin them.
8. **Elaborated statements** (`--elaborated`): the `pp.all` printout of each pinned theorem's
   type and of each pinned definition, with every name resolved, is compared with the printout
   obtained from the baseline file. A theorem may differ only by instance arguments removed from
   its leading binders, which is what `omit` does and which can only generalize it.

The check does not decide whether a statement is a faithful formalization of its source, nor
whether a proof follows the published argument.

## Rerunning the check

The script and the run files are not in the old commits, so take them from a current checkout.
For the statement, prefix, token and file checks no build is needed:

```bash
python3 experiments/fixed-statement/check_spec.py experiments/fixed-statement/runs/voter.json \
    --rev 81ad0433ab7679bc349f396819ca537568eb8c7f
```

For the full check, check out the accepted commit and run the script from there:

```bash
git worktree add --detach ../accepted 81ad0433ab7679bc349f396819ca537568eb8c7f
cd ../accepted/voter && lake exe cache get && cd ..
python3 <current checkout>/experiments/fixed-statement/check_spec.py \
    <current checkout>/experiments/fixed-statement/runs/voter.json --build --axioms --elaborated
```

All eight accepted commits use Lean 4.32.0 and the same Mathlib revision as the current packages.

### Results on the accepted commits

`check_spec.py RUN.json --build --axioms --elaborated` on a checkout of each accepted commit, and
`check_spec.py RUN.json --rev <accepted> --strict`, on 2026-11-04. Every run passes every check
with its own parameters (`SPEC OK`):

| Run | Statements, tokens, files | Build | Axioms | Elaborated statements | `--strict` |
| --- | --- | --- | --- | --- | --- |
| `voter` | OK | OK | OK | OK; 3 theorems generalized by `omit` | OK |
| `isothermal` | OK | OK | OK | OK | flags `SimpleGraph` appended to the `open` line |
| `push-pull` | OK | OK | OK | OK | OK |
| `reed-frost` | OK | OK | OK | OK | flags an added `open SimpleGraph` |
| `undecided` | OK | OK | OK | OK; 1 theorem generalized by `omit` | OK |
| `averaging` | OK; `open SimpleGraph` reported as reviewed | OK | OK | OK; 4 theorems generalized by `omit` | OK (same reviewed line) |
| `median-basics` | OK | OK, one warning outside the agent's files (a pinned `sorry` of the other median run) | OK | OK | OK |
| `two-choices` | OK; `import Median.BinaryAssembly` reported as reviewed | OK, eight warnings outside the agent's files (the pinned `sorry`s of the other median run) | OK | OK | OK (same reviewed line) |

"Generalized by `omit`" means that the elaborated statement equals the baseline's except for
dropped instance arguments: 3 in `voter`, 1 in `undecided` and 4 in `averaging`, one per
`omit … in` line the agent added. The `open` lines that `--strict` flags in `isothermal` and
`reed-frost` were not pinned by the scripts of those runs; the elaborated statements show that
they change none of the pinned declarations.

## The eight runs

| Run | Target | Agent | Pinned | Pinned commit | Accepted commit | Lines | Sessions | Time | Tool calls | Tokens | Cache reads |
| --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `voter` | voter consensus time | grok-4.7 | 4 defs, 7 thms | `7fcb31f` | `81ad043` | 367 | 1 | 32 min | 151 | 10.7M | 96.1% |
| `isothermal` | isothermal theorem | grok-4.7 | 10 defs, 8 thms | `d06dc8a` | `ae93883` | 848 | 1 | 78 min | 407 | 20.0M | 94.9% |
| `push-pull` | push vs pull fixation | grok-4.7 | 5 defs, 7 thms | `e58cb55` | `e91b598` | 631 | 1 | 33 min | 179 | 9.2M | 95.8% |
| `reed-frost` | Reed–Frost/percolation | grok-4.7 | 7 defs, 7 thms | `fa01243` | `431cec2` | 272 | 1 | 26 min | 162 | 11.4M | 97.4% |
| `undecided` | undecided-state basics | grok-4.7 | 8 defs, 6 thms | `cb62f04` | `5c232a4` | 327 | 1 | 27 min | 108 | 7.0M | 93.8% |
| `averaging` | averaging convergence | grok-4.7 | 3 defs, 5 thms | `f18d21d` | `4c62cd3` | 578 | 1 | 66 min | 412 | 18.7M | 95.7% |
| `median-basics` | median basics | GLM-5.3 | 9 defs, 8 thms | `dbe73d6` | `ce1e12f` | 301 | 5 | 34 min | 132 | 7.2M | not recorded |
| `two-choices` | 2-Choices w.h.p. | GLM-5.3 | 9 defs, 1 thm | `de93267` | `2f8db8c` | 2437 | 4 | 128 min | 276 | 45.8M | not recorded |

How the columns are measured (`run_metrics.py`, output in `metrics.md`):

* **Lines**: `wc -l` of the pinned file at the accepted commit; for `two-choices`, of
  `Binary.lean` and the four helper files the agent wrote.
* **Time**: agent time, from the first to the last logged event of each session, summed over the
  sessions of the run and rounded to the nearest minute. It includes the builds the agent ran, and
  not the pauses between sessions. For the Grok runs the events are those of the agent's session
  log, which has a timestamp per event. Vibe records only the start and end time of each session.
  From the first event of the first session to the last event of the last one, `median-basics`
  spans 123 min and `two-choices` 134 min.
* **Tool calls**: Grok: completed tool calls. Vibe: tool calls in the assistant messages, each
  message counted once. A resumed Vibe session replays the earlier messages, which are not counted
  again.
* **Tokens**: input tokens (cache reads included) plus output tokens, over all model calls.
  Grok's session log gives the totals. Vibe gives cumulative totals per session; a session that
  continues another one after a context compaction reports the totals of both, so the earlier
  session's are subtracted. Vibe does not record cache reads. Over the six Grok runs, 95.6% of
  the tokens were cache reads.

The Grok numbers agree with a second log (the agent's JSON output stream), whose tool calls and
final token totals are the same, and whose file times give run times within 3 s of the ones above.

### Sessions of the two GLM runs

`median-basics` (five sessions, prompts `median-basics.md` and `median-basics-resume.md`):

| Session | Time | Tool calls | Prompt | End |
| ---: | ---: | ---: | --- | --- |
| 1 | 17:09 | 48 | `median-basics.md` | a tool call written as text |
| 2 | 0:12 | 0 | session 1 resumed with `median-basics-resume.md` | a tool call written as text |
| 3 | 1:53 | 21 | `median-basics.md` | no final reply |
| 4 | 9:11 | 31 | `median-basics.md` | no final reply |
| 5 | 5:34 | 32 | `median-basics.md` | final summary, all eight theorems proved |

`two-choices` (four sessions):

| Session | Time | Tool calls | Prompt | End |
| ---: | ---: | ---: | --- | --- |
| 1 | 73:43 | 123 | `two-choices-1.md` | context compacted, continued in session 2 |
| 2 | 12:50 | 72 | written by Vibe after compacting the context of session 1: a summary of the conversation | no final reply |
| 3 | 39:36 | 66 | `two-choices-2-assembly.md` | no final reply |
| 4 | 2:19 | 15 | `two-choices-3-final.md` | final summary, `consensus_whp` proved |

Session 3 started from commit `3623307` ("WIP (not accepted)"), which records the files of
sessions 1 and 2. The prompts of sessions 3 and 4 were written between sessions. They repeat the
rules of the first prompt, state what the files already contain, and narrow the task to the
remaining step: assembling the phase lemmas (session 3), then deducing `consensus_whp` from the
lemma `binary_consensus` written in session 3 (session 4).

The two lines flagged by the context check, `open SimpleGraph` in `averaging` and
`import Median.BinaryAssembly` in `two-choices`, are listed under `reviewed` in their run files:
the check reports them and does not count them as violations.

### Sessions not counted

* Before `median-basics`, a one-command session tested the sandbox.
* Before the re-pin `de93267`, the statement of `consensus_whp` (pinned in `dbe73d6`) started from
  a 3/5 majority. Two GLM sessions worked on that statement; they are not part of `two-choices`.
* On the same two pinned files of `dbe73d6`, a Grok agent was started first. Both runs were
  interrupted by a usage limit after about 17 minutes and are not part of the table.

The session ids of the counted and uncounted sessions are in `runs/<run>.json`.
