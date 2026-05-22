# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C2.4.1
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First preserve the reviewed C2.4.0 stable checkpoint: inspect `git status --short` and staged diff, then commit only the relevant tracked source/task-memory changes already staged by `git add -u` if still appropriate; do not stage untracked scratch/probe files. After the commit, call `begin_component("C2.4.1")` and inspect the `Resume eval_all_type_sound_mutual[Expr_Builtin]` block before editing.
- expected_goal_shape: C2.4.0 is proved/reviewed; `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)` succeeded. PLAN says Oracle next is C2.4.1, the Expr_Builtin statement-soundness resume. Expect a semantic proof obligation in the Expr_Builtin resume, not the earlier prefix namespace/body type errors.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If the build regresses to source-prefix `body`/`exception` namespace errors, checkpoint_progress under C2.4.1 only if active and cite the regression; otherwise likely inspect whether the C2.4.0 commit/source was lost. If Expr_Builtin exposes missing builtin boundary lemmas or brittle unfolding pressure, close/checkpoint as appropriate and call plan_oracle rather than redesigning C2.4.1 locally.

## Do Not Retry
- Keeping theorem/evaluator statement-list variable named bare `body` and attempting `(body : stmt list)` annotations.: HOL can resolve the identifier as an imported word64 function before/as the type constraint is applied; consistent renaming to `body_stmts`/`body_fun` was the effective cleanup pattern.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42558_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42647_t001
  - evidence: episode:E0791
- Treating stale `body` vs `body_stmts`/`body'` quotation failures as semantic theorem failures or doing tactic search on them.: These were rename fallout/source elaboration mismatches. Fixing the local name/quotation made the theory build.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42593_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42647_t001
- Staging or committing all files blindly with `git add -A`.: There are many untracked scratch/probe files unrelated to the stable C2.4.0 checkpoint. Only tracked relevant source/task-memory changes should be committed after inspecting status/diff.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42650_t001
- Starting C2.4.1 proof edits before preserving the reviewed C2.4.0 checkpoint.: E0791 was accepted and the harness requested a stable checkpoint; tracked changes were staged but not committed before handoff.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42649_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42651_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box option not used: a local parser/type abbreviation or hiding/import change might avoid renaming `body`, but evidence shows simple local renaming works and is less invasive.
- We are not optimizing the wrong theorem now: C2.4.0 is done; next is the actual Expr_Builtin resume C2.4.1, as PLAN schedules.
- The PLAN decomposition still matches reality: source-prefix cleanup gate succeeded, then semantic Expr_Builtin proof is next. No need to rework assignment/call architecture for this issue.
- Do not retry C2.4.0 tactics or namespace edits without a new build regression. For C2.4.1, if builtin boundaries are missing, ask the strategist rather than inventing a parallel induction.
- A fresh expert should first question the working tree state: tracked changes are staged, untracked scratch files remain, and a clean logical commit should precede new proof edits. Then inspect the exact Expr_Builtin resume goal and available builtin boundary theorems.

### What Went Wrong
- C2.4.0 was successfully closed and reviewed, but the session stopped after I staged tracked changes with `git add -u` and before committing. Next session must not blindly stage untracked scratch files; inspect status/diff first.
- The local namespace issue was broader than the initially reported helper: once bare `body` collided with an imported word64 function, adjacent helper statements, proof witnesses, scope-bracket abstractions, For resume quotations, and the top-level `function_body_type_sound` theorem all needed consistent renaming or use of HOL-generated `body'` binders.
- I initially fixed failures one holbuild at a time; a bounded grep audit for bare `body` in statement-list evaluator positions would have shortened the cleanup.

### Ignored Signals
- Repeated HOL errors all had the same shape: `eval_stmts`/`type_stmts` expected `stmt list` but parsed `body` as a word64 function. This indicated a namespace pattern, not isolated proof failures.
- Renaming a theorem variable requires updating theorem statements, proof quotations (`qpat_x_assum`, `Cases_on`, `qmatch_*`), existential witnesses, and manually stated intermediate facts. Missing any of these causes proof mismatches that should not be treated as semantic failures.
- After component review accepted E0791, stable checkpoint discipline required committing before new proof work; I staged with `git add -u` but handoff interrupted before commit.

### Strategy Adjustments
- For C2.4.1, begin the component before any build/edit. Work only on Expr_Builtin semantics; do not continue broad namespace cleanup unless holbuild shows an actual regression.
- Use builtin/expression boundary lemmas for Expr_Builtin; avoid unfolding builtin internals unless a missing boundary is shown and escalated.
- If a proof branch forces many quoted assumptions or manual `qspecl_then` plumbing, treat that as a helper/interface smell and escalate, per PLAN guidance, instead of tactic-thrashing.

### Oracle Feedback
- Strategist's Risk-1 classification for C2.4.0 held: no definition or invariant change was needed; local renaming/qualification let `vyperTypeStmtSoundnessTheory` build.
- Plan review accepted E0791 without PLAN changes and scheduled C2.4.1 next. This confirms the prefix cleanup is complete and C2.4.1 should proceed as ordinary statement-soundness proof integration.
- The earlier strategist suggestion to annotate `(body : stmt list)` was less effective than renaming; evidence showed annotation did not override the imported/resolved `body` identifier, but the PLAN also permitted renaming.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42647_t001 - decisive `vyperTypeStmtSoundnessTheory` build success for C2.4.0
- episode:E0791 - C2.4.0 closed as proved after local body/exception namespace cleanup
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42649_t001 - strategist review accepted E0791 and directed next work to C2.4.1
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42652_t004 - query_plan shows active none, Oracle next/beginable C2.4.1
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42650_t001 - git status before handoff: tracked files modified and many untracked scratch/probe files present
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42651_t001 - `git add -u` was run before handoff, so tracked changes may be staged
