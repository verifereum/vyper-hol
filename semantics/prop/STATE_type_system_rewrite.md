# STATE_type_system_rewrite
Updated: 2026-06-03

## Cursor
- component: none
- status: ready
- active_file: none
- next_action: No further proof work is scheduled. PLAN shows C0.6 and C0.7 done, no active component/frontier, and completion was already proposed/accepted by end_session processing. If a new session nevertheless resumes, first inspect query_plan and git status; do not edit/build unless a new PLAN component is created.
- expected_goal_shape: No HOL goal expected; task-scoped C0 tail is complete. Last focused successful build was `vyperTypeStmtSoundnessTheory`; a later build attempt was refused only because no PLAN frontier remained.
- verify_with: query_plan(); git status --short; last clean proof build evidence is tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t004

## If This Fails
- If query_plan unexpectedly shows remaining frontier/work, follow the PLAN gate and begin exactly Oracle next. If tracked diffs unexpectedly appear, inspect and either commit task-owned bookkeeping unsigned or report repo-state issue; do not stage untracked legacy/scratch files.

## Do Not Retry
- Do not resume C0.6 from old STATE instructions about an unverified `mp_tac raw_call_bytes_slot_size_bound` edit.: Those instructions are stale; C0.6 was proved, reviewed, and committed. The final successful proof uses `Q.SPEC` over `GEN_ALL raw_call_bytes_slot_size_bound`, `simp[]`, `TRY strip_tac`, and `LENGTH_TAKE_EQ`.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6080_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6082_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6086_t001
- Do not chase the holbuild `∃ $var. ¬$var` wrapper by changing the opening of the Resume proof.: It was an instrumentation wrapper around deeper failed subgoals; nested logs exposed the real size/value goals, and the opening proof was sound.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6077_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6080_t001
- Do not stage or commit `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are untracked legacy/scratch artifacts; all reviewed task-owned tracked changes have already been committed unsigned.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6106_t002
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6104_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6104_t002
- Do not call holbuild without an active/new PLAN component after completion just to re-verify.: The harness blocks builds when no executable frontier remains. Use the existing clean build evidence unless a new PLAN component is created.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t004
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6103_t002
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6103_t003

## Reflection
### Tunnel Vision Check
- Outside-the-box approach considered during C0.6 was extracting a full RawCall tail helper, but final reality showed only a small slot-size/destructor boundary was needed; avoid over-engineering if future RawCall variants reduce to small typed-value/length facts.
- A fresh expert should first question whether any remaining `cheat` grep hit is executable or merely a comment. The final audit found only a historical comment at `vyperTypeStmtSoundnessScript.sml:2715`.
- The PLAN decomposition is now complete for C0: C0.6 RawCallTarget proof and C0.7 final audit are both reviewed proved; no helper/definition redesign is needed unless a future broader task creates new obligations.
- Do not optimize a non-existent next theorem: query_plan has no frontier. Any future work requires a new task/PLAN update, not continuing local proof search.

### What Went Wrong
- STATE at handoff still contained stale C0.6 in-progress instructions because completion occurred before handoff rendering; the durable truth is in PLAN/DOSSIER: C0.6 E0332 and C0.7 E0333 are proved/reviewed.
- During C0.6, initial attempts used `drule`/unspecialized `mp_tac` on `raw_call_bytes_slot_size_bound`; those did not match because the local theorem had a free variable and the live goal needed explicit specialization at `flags.rcf_max_outsize`.
- Several holbuild outputs reported a top-level `∃ $var. ¬$var` wrapper; the useful goals were nested in instrumented logs. Chasing the wrapper would have been wrong.
- Final oracle-tag audit via expected generated `*Theory.txt` paths could not be performed because `.holbuild/gen`/`.holbuild/objs` and project `*Theory.txt` were absent in this layout; strategist accepted this as non-blocking given clean focused build and source-level cheat audit.

### Ignored Signals
- The repeated dynamic bytes/tuple goals initially signaled a boundary lemma need. This was resolved by the small `raw_call_bytes_slot_size_bound` helper rather than more inline arithmetic thrashing.
- The old STATE do-not-commit warning became stale after C0.6 built cleanly and was reviewed; git status/log and DOSSIER supersede it.
- Untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` remain; they are scratch/legacy artifacts and were intentionally not staged.

### Strategy Adjustments
- For future RawCall-like branches, derive argument destructors from `exprs_runtime_typed` in a small local lemma and use `LENGTH_TAKE_EQ` for `LENGTH (TAKE n xs) <= n` goals.
- When applying a local theorem with free variables, use `GEN_ALL` plus explicit `Q.SPEC` rather than hoping `drule`/`mp_tac` will infer the intended instantiation.
- For completion after a terminal audit, commit only reviewed Dossier/Learnings/bookkeeping with `git commit --no-gpg-sign`; never `git add -A`.
- If a future session resumes after completion, treat query_plan's no-frontier state as authoritative and avoid builds/edits unless a new PLAN component exists.

### Oracle Feedback
- Held: the strategist's C0 tail rebase was correct; C0.6 had to finish before C0.7.
- Held: the maintainer-approved linear, branch-local style was sufficient for RawCallTarget once small destructor/slot-size facts were added.
- Held: C0.7 audit criteria were enough for task completion; strategist accepted missing generated Theory.txt path audit as non-blocking because focused holbuild and source grep were clean.
- Potential miss resolved: C0.6 did not require a full RawCall tail-result helper; a compact slot-size helper plus explicit specialization closed the remaining goals.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6080_t001 - C0.6 focused build clean after RawCallTarget proof
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6082_t001 - strategist accepted C0.6 proved episode E0332
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6086_t001 - unsigned commit 166a02d19 for RawCallTarget proof/source progress
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t004 - C0.7 final focused holbuild succeeded
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t001 - cheat grep found only historical comment, no executable cheat
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6092_t002 - source read confirms ExtCall nonstatic and RawCallTarget Resume bodies are proofs
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6098_t001 - strategist accepted C0.7 final audit episode E0333
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6102_t001 - unsigned final Dossier/Learnings bookkeeping commit 81fe819d4
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6103_t003 - PLAN has no active component/frontier; completion allowed
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6106_t002 - git status has only untracked legacy/scratch files, no tracked diffs
