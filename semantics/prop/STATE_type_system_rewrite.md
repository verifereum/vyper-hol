# STATE_type_system_rewrite
Updated: 2026-06-03

## Cursor
- component: none
- status: ready
- active_file: none
- next_action: No proof work remains. If a new session resumes, first run query_plan() and git status --short; do not edit or build unless a new PLAN component/frontier is created. If PLAN still shows no frontier, propose end_session(outcome='complete').
- expected_goal_shape: No HOL goal expected. PLAN has no scheduled leaf frontier, no active component, C0.6 and C0.7 are done/reviewed, and the last accepted focused proof build was vyperTypeStmtSoundnessTheory clean.
- verify_with: query_plan(); git status --short; use prior clean build evidence tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t004 unless a new PLAN component authorizes holbuild

## If This Fails
- If query_plan unexpectedly shows a beginable frontier, follow the PLAN gate and begin exactly Oracle next before edits/builds. If tracked diffs appear, inspect them and either commit only task-owned stable bookkeeping with git commit --no-gpg-sign or report a repo-state issue. Do not stage untracked legacy/scratch files.

## Do Not Retry
- Resume C0.6 from stale instructions about an unverified mp_tac raw_call_bytes_slot_size_bound edit.: C0.6 was already proved, reviewed, and committed; final proof used explicit Q.SPEC over GEN_ALL raw_call_bytes_slot_size_bound, simp[], TRY strip_tac, and LENGTH_TAKE_EQ.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6080_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6082_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6086_t001
- Chase the holbuild `∃ $var. ¬$var` wrapper by changing the opening of the Resume proof.: The wrapper was instrumentation around deeper failed subgoals; nested logs exposed the real size/value goals and the opening proof was sound.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6077_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6080_t001
- Stage or commit semantics/prop/LEARNINGS_type_system_rewrite.legacy.md or semantics/prop/tmp_helper.txt.: They are untracked legacy/scratch artifacts; reviewed task-owned tracked changes have already been committed unsigned.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6106_t002
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6112_t001
- Run holbuild after completion without an active/new PLAN component just to re-verify.: The structured PLAN gate has no executable frontier; rely on accepted clean build evidence unless a new PLAN component authorizes proof work.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t004
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m6114_t002

## Reflection
### Tunnel Vision Check
- Outside-the-box approach considered during C0.6 was extracting a full RawCall tail helper, but final reality showed only a compact slot-size/destructor boundary was needed; avoid over-engineering future RawCall-like branches if small typed-value/length facts suffice.
- A fresh expert should first question whether any remaining cheat grep hit is executable or just a historical comment; the final audit found only a historical comment at vyperTypeStmtSoundnessScript.sml:2715.
- The PLAN decomposition is complete for this task-scoped C0 tail: C0.6 RawCallTarget proof and C0.7 final audit are both reviewed proved. No helper/definition redesign is indicated unless a future task creates new obligations.
- Do not optimize a non-existent next theorem. query_plan has no frontier; future proof work requires a new task/PLAN update, not local proof search.

### What Went Wrong
- Earlier STATE handoff content lagged behind completed proof reality; the durable truth is now PLAN/DOSSIER evidence: C0.6 E0332 and C0.7 E0333 are proved/reviewed.
- During C0.6, initial attempts with drule/unspecialized mp_tac on raw_call_bytes_slot_size_bound did not match because the local theorem had a free variable and the live goal needed explicit specialization at flags.rcf_max_outsize.
- Several holbuild failures displayed a top-level existential wrapper (`∃ $var. ¬$var`); the useful proof goals were nested in instrumented logs. Chasing the wrapper would have been misleading.
- Final oracle-tag audit via expected generated *Theory.txt paths could not be performed in this layout; strategist accepted this as non-blocking because focused holbuild and source-level cheat audit were clean.

### Ignored Signals
- Repeated dynamic bytes/tuple goals initially signaled need for a small boundary lemma rather than continued inline arithmetic search; this was resolved by raw_call_bytes_slot_size_bound plus explicit specialization.
- Old do-not-commit warnings became stale after C0.6 built cleanly and was reviewed; git status/log and DOSSIER superseded them.
- Untracked semantics/prop/LEARNINGS_type_system_rewrite.legacy.md and semantics/prop/tmp_helper.txt remain scratch/legacy artifacts and should stay untracked unless an operator explicitly asks otherwise.

### Strategy Adjustments
- For future RawCall-like branches, derive argument destructors from exprs_runtime_typed in a small local lemma and use LENGTH_TAKE_EQ for LENGTH (TAKE n xs) <= n goals.
- When applying a local theorem with free variables, use GEN_ALL plus explicit Q.SPEC rather than hoping drule/mp_tac will infer the intended instantiation.
- For completion after a terminal audit, commit only reviewed task-owned bookkeeping/source changes with git commit --no-gpg-sign; never git add -A.
- If a future session resumes after completion, treat query_plan's no-frontier state as authoritative and avoid builds/edits unless a new PLAN component exists.

### Oracle Feedback
- Held: strategist's C0 tail rebase was correct; C0.6 had to finish before C0.7.
- Held: maintainer-approved linear, branch-local style was sufficient for RawCallTarget once small destructor/slot-size facts were added.
- Held: C0.7 audit criteria were enough for task completion; strategist accepted missing generated Theory.txt path audit as non-blocking given clean focused build and source audit.
- Potential miss resolved: C0.6 did not require a full RawCall tail-result helper; compact slot-size helper plus explicit specialization closed remaining goals.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6114_t002 - current PLAN has no frontier/active component; C0.6 and C0.7 are done
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6114_t001 - current STATE cursor and do-not-retry guidance
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t004 - final focused vyperTypeStmtSoundnessTheory holbuild succeeded
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6091_t001 - final cheat grep found only a historical comment, no executable cheat
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6098_t001 - strategist accepted C0.7 final audit episode E0333
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6111_t001 - final STATE bookkeeping commit was made unsigned
- tool_output:TO_type_system_rewrite-20260602T195240Z_m6112_t001 - git status after commit had only untracked legacy/scratch files
