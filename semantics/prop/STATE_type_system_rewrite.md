# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C3.1
- status: ready
- active_file: semantics/prop/vyperTypeBuiltinsScript.sml
- next_action: Do not edit/build before preserving stable checkpoint. First inspect `git status --short` and `git diff --cached --stat`; tracked relevant source/task-memory changes are already staged from the prior C2.3 Pop repair plus PLAN/DOSSIER/LEARNINGS updates, while STATE will be rewritten by this handoff and must be staged with `git add -u semantics/prop/STATE_type_system_rewrite.md` if committing. Do not stage untracked scratch files. If the staged diff is still only stable task-owned progress, commit it with a small checkpoint message. Then begin_component('C3.1') and inspect `well_typed_binop_no_type_error` / nearby binop helpers in `vyperTypeBuiltinsScript.sml` before building.
- expected_goal_shape: No live proof goal. Rebased PLAN frontier says C3.1 is Oracle next: close binop no-TypeError boundary lemmas, especially `well_typed_binop_no_type_error` and any immediate `well_typed_update_binop_no_type_error` corollary. Expect any build failure to be in `vyperTypeBuiltinsTheory` near binop/builtin boundaries or later residual C4 branches.
- verify_with: After commit and begin_component('C3.1'), use `holbuild(targets=["vyperTypeBuiltinsTheory"], timeout=600)` for the C3.1 proof loop; C0/C1 carry-forward checks already passed with statement/assignment wrapper targets.

## If This Fails
- If the first C3.1 build fails outside binop no-TypeError/update-binop obligations, checkpoint_progress on C3.1 with the holbuild output and ask strategist only if the failure is outside the component coverage. If a binop proof attempt starts requiring broad `gvs[evaluate_binop_def, AllCaseEqs()]` across all operators or creates huge goals, stop and use per-operator helper style from the PLAN/DOSSIER instead of tactic thrashing.

## Do Not Retry
- Start editing/building C2.4 or C2.5 before C3/C4 boundary components close.: Whole-plan rebase made C2.4/C2.5 consumers dependent on C3/C4. Proving them first risks hidden CHEAT dependencies or forbidden builtin/type-builtin case analysis in statement soundness.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40825_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40826_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40839_t005
- Use one giant `gvs[evaluate_binop_def, AllCaseEqs()]` over every binop case in C3.1.: Prior evidence and PLAN warn this causes case explosion/timeouts and brittle F-goals; C3.1 should use per-operator/local helper boundaries instead.
  - evidence: episode:E0138
  - evidence: episode:E0141
  - evidence: episode:E0145
- Stage or commit untracked scratch files such as `test_*`, `test_conj*`, or `SuspBugProbeScript.sml`.: They are ad-hoc scratch files unrelated to the stable proof checkpoint. Only tracked task-owned source/memory changes should be committed.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40839_t002
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40819_t002
- Assume old C2.4 dossier entries prove the current `Expr_Builtin` source cheat.: C2.4 component identity drifted; strategist invalidated stale C2.4 iterator/Append evidence for current `Expr_Builtin`. Source is authoritative.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40822_t003
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40823_t001
- Reopen the completed Expr_Pop proof or reintroduce the old assignability proof from `assignable_type_def`.: C2.3.6 is proved/reviewed; Pop assignability must come from `well_typed_expr_Pop_dynamic_target_assignable` and result typing from `assign_target_pop_success_some_typed`. Reopening it would waste time unless a build regression appears there.
  - evidence: episode:E0729
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40813_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40815_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box: before proving C3.1, ask whether current source already has some binop proofs from earlier sessions; read the local theorem region and generated theorem index rather than assuming the old dossier's C1.1 history maps exactly to current C3.1.
- A fresh expert should question whether C3.1's theorem still contains an actual `cheat` or whether the remaining CHEAT path is now a downstream wrapper; use source grep/build after begin_component to verify.
- Do not optimize the wrong layer: C2 statement expression resumes are blocked on C3/C4 boundaries, so proving them first is the wrong abstraction even if they are visible cheats in source.
- If C3.1 needs many arithmetic/value-typing side lemmas, check existing `vyperEvalBinopScript.sml`, prior local helpers, and dossier evidence before inventing new broad tactics.
- The PLAN decomposition now looks better than the previous over-augmented C2 tree, but if C3.1 again becomes a sequence of exposed constructor residuals, close/checkpoint and request decomposition rather than chasing unplanned residuals indefinitely.

### What Went Wrong
- At session start, source and PLAN were out of sync: old C2.4 dossier entries said proved for unrelated iterator/Append work while current source had `Expr_Builtin` and `Expr_TypeBuiltin` cheats. Following query_plan's decomposition-pressure instruction avoided starting the wrong proof.
- Local C2.5 rebase was insufficient because type-builtin statement soundness depends on C4 boundary theorems across top-level siblings. The strategist correctly requested a whole-plan rebase instead of another local child decomposition.
- I staged tracked files with `git add -u` just before the handoff signal. This is okay only if next session inspects the staged diff and commits the stable checkpoint before starting C3.1; untracked scratch files must remain unstaged.

### Ignored Signals
- The old STATE still described C2.4 as blocked by decomposition pressure; after rebase, query_plan now points to C3.1. Next session should trust query_plan/PLAN plus source reality, not stale STATE text before this handoff.
- C2.4/C2.5 being scheduled before C4 was a dependency-order smell. It would have forced forbidden builtin/type-builtin case analysis in statement soundness or hidden CHEAT dependencies.
- The apparent C2.4 'proved' history was misleading because component identity drifted; source-authoritative cheats must override stale dossier status.

### Strategy Adjustments
- The whole PLAN is now rebased so C3 update/binop work and C4 builtin/type-builtin boundaries precede C2 consumer resumes. Follow this order strictly.
- For C3.1, prefer existing per-operator binop helper style and theorem-boundary proofs. Do not expand `evaluate_binop_def` over all operators in one giant simplification.
- Commit stable reviewed C0/C1 carry-forward plus prior C2.3 Pop work before new proof edits, if status/diff confirms only task-owned stable changes are staged.
- Keep C2 `Expr_Builtin`/`Expr_TypeBuiltin` as small consumers after C4; if a C2 proof needs `evaluate_builtin_def`, escalate as a C4 boundary-interface problem.

### Oracle Feedback
- C2.4 local rebase accepted: current `Expr_Builtin` is a C4.2/C3.3-dependent consumer; stale C2.4 iterator/Append evidence is invalid for it.
- C2.5 local rebase was rejected with whole-plan review requested; this strategist insight held and produced a coherent reordering: C3 then C4, then C2 consumers.
- C0 and C1 carry-forward closures E0730/E0731 were accepted with no PLAN changes after successful holbuild checks. These do not certify final zero-CHEAT; C3/C4/C2/C5/C6/C7 remain required.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40823_t001 - C2.4 rebase accepted; Expr_Builtin depends on C4.2/C3 boundaries and stale C2.4 evidence invalidated
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40825_t001 - C2.5 local rebase rejected; whole-plan review required due cross-top-level C4 dependencies
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40826_t001 - whole-plan rebase installed; C3/C4 scheduled before C2 builtin/type-builtin consumers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40829_t001 - C0 carry-forward check: `vyperTypeStmtSoundnessTheory` built successfully
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40831_t001 - strategist accepted C0/E0730 closure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40833_t001 - C1 carry-forward check: `vyperTypeAssignSoundnessTheory` built successfully
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40835_t001 - strategist accepted C1/E0731 closure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40839_t005 - final handoff query_plan: beginable/Oracle next is C3.1
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40839_t002 - git status: tracked files staged, STATE unstaged, many untracked scratch files present
- episode:E0730 - C0 closed proved as rebased carry-forward audit
- episode:E0731 - C1 closed proved as rebased assignment-target/wrapper carry-forward
