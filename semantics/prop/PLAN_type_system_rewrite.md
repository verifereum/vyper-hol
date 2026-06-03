# PLAN

## Structured Components

### C0: Task-scoped type-system rewrite tail after ExtCall completion
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk 2: the old ExtCall blocker is closed and reviewed through E0330; the only remaining proof work in the task-scoped call-expression region is the single RawCallTarget Resume, followed by a mechanical audit. This replacement removes stale completed descendants from the active scheduler and preserves their evidence as carried-forward context.
- Required for completion: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0, C0.1, C0.2, C0.3, C0.4, C0.5, C0.5.5, E0330
- Invalidates prior progress/evidence: TO_type_system_rewrite-20260602T195240Z_m6002_t001, TO_type_system_rewrite-20260602T195240Z_m6003_t001

#### Progress note
This is an ancestor/tail rebase, not a new proof strategy. All completed ExtCall/static/nonstatic evidence remains valid and is carried forward as historical support, but the old deep C0 child structure is intentionally omitted so the scheduler cannot choose the final audit before RawCallTarget. The stale C0.7-beginable state is invalidated.

#### Summary
- Rebased task-scoped C0 to the actual remaining tail in `semantics/prop`.
- Completed ExtCall work, including the nonstatic success integration and terminal audit E0330, is carried forward as historical evidence rather than active descendants.
- The next and only proof-development leaf is C0.6: close `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
- C0.7 is strictly a final audit/commit leaf and depends on C0.6.
- No files outside `semantics/prop` may be edited; no evaluator/semantics definitions may be changed; commits must be unsigned.

#### Approach
Proceed linearly: begin C0.6 next, prove RawCallTarget, then begin C0.7. Treat E0330 as the ExtCall checkpoint; do not attempt to rerun or replan completed ExtCall components unless the focused build shows they regressed.

#### Not to try
Do not begin C0.7 before C0.6 is closed. Do not retain the old deep completed C0 descendants as active scheduler nodes just to document history; that caused the frontier contradiction. Do not broaden the task to unrelated repository cheats or change semantics definitions.

#### Argument
The task-scoped rewrite has already reduced the relevant call-expression soundness work to a linear tail. Prior completed C0 descendants established the fresh-stack infrastructure, removed the localized raw-call return-type well-formedness cheat, and closed/audited the ExtCall static and nonstatic branches; E0330 is the current stable checkpoint for that history. The source still contains an executable cheat at `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`, so proof completion must first close that branch. Only after RawCallTarget is proved can a final integrity audit soundly claim that the task-scoped call/statement proof obligations contain no remaining executable cheat. Therefore the remaining dependency graph is exactly C0.6 -> C0.7.

#### Definition design
No definitions are to be changed. The proof interface is the existing mutual `eval_all_type_sound_mutual` Resume structure in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, plus existing local helper facts such as `raw_call_return_type_well_formed`. C0.6 may use current evaluator/type definitions by controlled, branch-local rewriting of the RawCallTarget case. If the RawCallTarget proof exposes a missing compact helper, the executor must stop with NEW_DEPENDENCY rather than inventing a broad generated-prefix adapter or changing semantics definitions.

#### Code structure
All edits remain under `semantics/prop`. C0.6 edits should be localized around `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` and, only if absolutely necessary after escalation, nearby local helper lemmas in the same proof script or task-local prop scripts. C0.7 may update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` progress notes and perform the final commit, staging only task-owned `semantics/prop` tracked changes with GPG signing disabled. Do not edit evaluator/semantics definitions and do not clean unrelated repository cheats.

### C0.6: Close RawCallTarget statement-expression soundness cheat after ExtCall integration
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Risk 2: RawCallTarget is one remaining expression-call branch in the same proof region and should be branch-local. Existing infrastructure includes `raw_call_return_type_well_formed`, and the ExtCall instability that previously blocked call-case work has been closed by E0330. If the proof requires a nontrivial helper, that is a NEW_DEPENDENCY escalation, not license for brittle theorem plumbing.
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.6, C0.2, C0.5.5, E0330

#### Progress note
Same RawCallTarget obligation as the prior C0.6; it is now rebased as the first tail leaf with no active dependency on omitted completed nodes. C0.2 supplies the raw-call return-type well-formedness fact; E0330 supplies the ExtCall-completion checkpoint.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` and remove its executable `cheat`.
- This is the immediate next component after the C0 rebase.
- Use the combined mutual postcondition: preservation/runtime consistency, no-TypeError, and result typing together.
- Use existing `raw_call_return_type_well_formed` rather than reproving return-type well-formedness.
- Split the raw-call evaluator chain linearly and close error cases immediately.
- Stop if a compact RawCall helper is needed; do not build long proof plumbing.

#### Description
The current focused source still has `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]: cheat`. This leaf owns exactly that proof. It should be attempted only as a careful branch-local Resume proof, using the same fresh-stack mutual soundness conventions as neighboring call branches (`RawLog`, `RawRevert`, `Send`, and the completed ExtCall branches).

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  ...
QED
```

#### Approach
Start by rewriting the RawCallTarget `well_typed_expr` case once to expose the typed arguments, flags, and raw-call return-type facts. Then move the `eval_expr` equation to the goal and unfold only the RawCallTarget evaluator prefix needed for the next monadic operation (`evaluate_def`, `bind_def`, `ignore_bind_def`, `type_check_def`, `assert_def`, `return_def`, `raise_def`, relevant raw-call operations). Destruct one operation at a time, close every error/no-update branch immediately with the mutual postcondition definitions, and keep a single success path active; in the success result-typing branch use `raw_call_return_type_well_formed` directly.

#### Not to try
Do not unfold retired old type-soundness theories or rely on legacy `vyperTypeSoundnessScript` facts unless already imported and clearly compatible. Do not weaken result typing, change `raw_call_return_type_def`, or change evaluator/semantics definitions. Do not broad-clean the whole evaluator prefix with global `simp`/`gvs`/`AllCaseEqs()` if it causes branch explosion. Do not manually assemble long `MATCH_MP`/`CONJ` theorem plumbing; escalate for a compact helper if that becomes necessary.

### C0.7: Final fresh-stack proof-integrity build, cheat audit, and task-local unsigned commit
- Kind: `final_audit`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: Risk 1: after C0.6 is proved, this is a mechanical grep/build/status/commit audit. It is deliberately blocked by C0.6 so the scheduler cannot treat a build-through-cheat as final completion.
- Dependencies: C0.6
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0.7, E0330
- Invalidates prior progress/evidence: TO_type_system_rewrite-20260602T195240Z_m6002_t001

#### Progress note
This replaces the prior C0.7 scheduling state. The audit concept and ExtCall audit evidence remain valid, but C0.7 must be non-beginable until C0.6 closes RawCallTarget.

#### Summary
- Final audit for the task-scoped type-system rewrite proof region in `semantics/prop`.
- Must run only after C0.6 proves the RawCallTarget Resume and removes the executable cheat.
- Verify focused HOL build succeeds and grep shows no remaining executable `cheat` in the planned call/statement soundness obligations.
- Confirm completed ExtCall proof architecture remains within the maintainer clarification: no broad generated-prefix adapter or forbidden global prefix cleanup.
- Check tracked edits are confined to `semantics/prop`, update progress notes if needed, and make an unsigned commit only after the audit passes.

#### Description
This component is terminal integrity work, not proof development. If any task-scoped executable cheat remains, especially at `Expr_Call_ExtCall_nonstatic_success` or `Expr_Call_RawCallTarget`, the component must fail/escalate rather than being marked complete. It may update task-local plan/progress notes and perform the required unsigned commit after successful verification.

#### Statement
Postcondition/audit obligation:

```text
1. `holbuild semantics/prop/vyperTypeStmtSoundnessTheory` or the focused target used for this task succeeds.
2. Grep/audit confirms no remaining executable `cheat` in task-scoped `eval_all_type_sound_mutual` call/statement proof obligations, in particular none at `Expr_Call_ExtCall_nonstatic_success` and none at `Expr_Call_RawCallTarget`.
3. No forbidden ExtCall proof architecture has been reintroduced: no broad generated-prefix adapter theorem and no recovery of the optional-driver premise by global `simp`/`gvs`/`AllCaseEqs()` over the ExtCall prefix.
4. Tracked modifications are confined to `semantics/prop`.
5. Progress notes are updated as needed and any commit is made unsigned, e.g. with GPG signing explicitly disabled.
```

#### Approach
After C0.6 completes, grep for `cheat`, `Expr_Call_ExtCall_nonstatic_success`, `Expr_Call_RawCallTarget`, and any forbidden ExtCall bridge/scaffold names noted in the task plan. Run the focused `holbuild`, inspect `git status --short` and relevant diffs, update only `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` if progress notes are missing, then stage only task-owned `semantics/prop` changes and commit with GPG signing disabled. If build or grep fails, report the concrete evidence and do not commit.

#### Not to try
Do not begin this component while C0.6 is not done. Do not treat a successful build that still contains `cheat` as proof completion. Do not edit evaluator/semantics definitions, files outside `semantics/prop`, or unrelated repository cheats. Do not use the final audit as a place to continue RawCallTarget proof development; return to C0.6/escalate instead.
