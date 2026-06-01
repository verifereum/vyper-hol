# PLAN

## Structured Components

### C0: Prove the ExtCall result branch of mutual expression type soundness under the narrowed maintainer authorization
- Kind: `proof_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The previous stop gate is superseded by the task clarification: a linear one-operation-at-a-time proof is now authorized. Risk is standard, not high, because the file already contains task-local ExtCall helper lemmas (`extcall_static_args_runtime_typed_dest`, `extcall_nonstatic_args_runtime_typed_dest`, `extcall_success_continuation_sound_cond_driver_ih`, `type_place_expr_Call_ExtCall_NONE`) and the new plan first proves a tiny argument-error boundary probe before entering success branches. The E0072 timeout remains binding negative evidence and is handled by prohibiting raw Resume simplification and broad generated-prefix cleanup.
- Required for completion: yes
- Supersedes: C0, C0.1, C0.2, C0.3, E0072, E0075
- Progress transition: `replacement`
- Carries progress/evidence from: E0072, TO_type_system_rewrite-20260601T081233Z_m1655_t001, TO_type_system_rewrite-20260601T081233Z_m1689_t001
- Invalidates prior progress/evidence: old C0 blocked_report_subtree completion as final task state

#### Progress note
The old C0 reporting/audit/commit work remains valid evidence of what failed, but it no longer supplies a complete task plan after the maintainer clarification authorized a careful linear ExtCall proof. Carry E0072 forward only as a constraint on the proof interface: do not retry the sanitized shell that left the generated optional-driver prefix live in an argument-error branch.

#### Summary
- Replace the completed stop/report C0 subtree with an executable proof-completion subtree for `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` only.
- Stay entirely inside `semantics/prop`; do not change evaluator/semantics definitions or files outside the task scope.
- First validate a tiny boundary lemma/probe that closes the `eval_exprs` argument-error path without exposing the generated optional-driver prefix.
- Then prove the ExtCall Resume by stepping through the monadic chain linearly: argument evaluation, target/value/calldata/account/run/revert/update, then only at the final return-data continuation specialize the optional-driver IH.
- The place-expression half is mechanical via `type_place_expr_Call_ExtCall_NONE`.
- E0072 remains a hard constraint: no broad top-level simplification, no whole-prefix adapter theorem, no static/nonstatic branch work until the argument-error probe builds.

#### Description
This component is task-scoped to the remaining ExtCall result cheat at `semantics/prop/vyperTypeStmtSoundnessScript.sml:17231`. The nearby `RawCallTarget` cheat is not pulled into this C0 replacement unless a separate task/ancestor component authorizes it. The new proof must respect the maintainer clarification: careful branch-by-branch proof is allowed, but the failed strategy of recovering the optional-driver premise from the top-level Resume context is still forbidden. The executor should update the task-local plan/state notes before proof edits so future sessions do not treat the old no-frontier stop report as authoritative.

#### Approach
Use the already-proved local helper layer around lines 9583-9821 where possible, especially the ExtCall return-continuation helpers and the static/nonstatic argument typing destructors. In the Resume, extract the expression-list IH and the optional-driver IH as named assumptions, but do not simplify the full generated optional-driver prefix at the top. Normalize only one monadic operation at a time and immediately close each error case; the optional-driver IH may be specialized only in the final branch with `returnData = [] /
IS_SOME drv` after account/transient updates have been split.

#### Not to try
Do not retry the E0072 sanitized shell (`well_typed_expr` one-step rewrite, `eval_exprs` split, explicit expression-list IH discharge, then `simp[no_type_error_result_def]` on the raw `args_res = INR y` goal). Do not use broad `simp`, `gvs`, `AllCaseEqs()`, or whole-prefix cleanup over the entire ExtCall prefix. Do not introduce or resurrect a long generated-prefix adapter theorem as the main proof interface. Do not edit evaluator definitions or files outside `semantics/prop`. Do not use signed commits.

#### Argument
The ExtCall evaluator first evaluates argument expressions. If that returns `INR`, the whole call returns the same error state immediately; this branch does not semantically depend on target decoding, external-call execution, return decoding, or the optional-driver IH. If argument evaluation succeeds with values `vs`, typing of the call gives either `MAP expr_type es = Address :: arg_types` for static calls or `Address :: Uint256 :: arg_types` for nonstatic calls. Together with `exprs_runtime_typed`, the existing destructors provide the concrete target address and, for nonstatic calls, the value amount, so the `dest_AddressV`/`dest_NumV` TypeError branches are unreachable. The remaining monadic operations either fail with runtime errors (which are automatically non-TypeError once the branch is split) or reach the success continuation. Account/transient updates preserve the runtime invariant using existing update/external-call preservation facts; only the final continuation may call `eval_expr cx (THE drv)`, and only when `returnData = []` and `drv` is present. At that point the generated optional-driver IH is semantically needed and may be specialized against the updated state; all earlier branches must avoid it.

#### Definition design
No evaluator or semantics definitions should change. Add only proof-local boundary lemmas in `vyperTypeStmtSoundnessScript.sml`, near the existing ExtCall helper block before the `Resume` section. The first boundary probe should expose a very small interface such as `eval_extcall_args_error`: from `eval_exprs cx es st = (INR y,args_st)`, one-step unfolding of `evaluate_def` for `Call ret_type (ExtCall ...) es drv` returns `(INR y,args_st)`. This lemma is a proof-interface test: if it cannot be proved by one-step evaluator unfolding and monad simplification without generated optional-driver context, stop and escalate. Subsequent branch lemmas should consume concrete branch facts and return the final soundness tuple directly; consumers should use `irule`/`drule`, not re-unfold the full ExtCall evaluator prefix repeatedly.

#### Code structure
All edits must remain under `semantics/prop`. Put new local ExtCall proof helpers in `semantics/prop/vyperTypeStmtSoundnessScript.sml` in the existing ExtCall helper area around the current `extcall_*` lemmas, before the mutual `Resume` block. Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and `semantics/prop/STATE_type_system_rewrite.md` to record that the old stop/report C0 subtree has been superseded by the maintainer clarification and this new linear proof boundary. Verify with `holbuild build vyperTypeStmtSoundnessTheory`; after a successful checkpoint with intentional edits only, commit with `git commit --no-gpg-sign` and stage only task-owned tracked files under `semantics/prop`.

### C0.1: Update task-local plan/state to supersede the old ExtCall stop report
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Documentation-only update inside `semantics/prop` based directly on the maintainer clarification and this replacement C0 plan.
- Supersedes: old C0.1, old C0.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0075
- Invalidates prior progress/evidence: old no-executable-frontier stop as current plan state

#### Progress note
The prior report/commit remains historically accurate, but the task now supplies authorization for a different proof boundary. This component changes the current-state notes, not the theorem proof.

#### Summary
- Edit only `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and/or `semantics/prop/STATE_type_system_rewrite.md`.
- Record that the old ExtCall stop gate is superseded by the maintainer clarification.
- Preserve E0072 as negative evidence: the failed generated-prefix boundary must not be retried.
- State the new required first proof step: the small argument-error boundary probe.
- Preserve the restrictions: no evaluator changes, no files outside `semantics/prop`, no signed commits.

#### Statement
Documentation deliverable: task-local plan/state files no longer say that no proof/build/edit action is legal merely because old C0 is complete; they direct the executor to the new C0.2 boundary probe and linear ExtCall proof plan.

#### Approach
Make a small dated update near the existing ExtCall generated-prefix blockage section and cursor/state block. Do not delete the old evidence; mark it as superseded for current scheduling but still binding as `not_to_try` evidence. Mention the exact first executable proof probe (`eval_extcall_args_error` or equivalent).

#### Not to try
Do not rewrite the whole roadmap or plan unrelated cheats. Do not claim the ExtCall theorem is proved. Do not stage untracked scratch/legacy files.

### C0.2: Prove the live argument-error boundary probe for ExtCall
- Kind: `proof_boundary_probe`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: This is deliberately tiny and tests exactly the E0072 failure mode outside the generated Resume context. The ExtCall evaluator returns immediately when `eval_exprs` returns `INR`, so the proof should be one-step evaluator unfolding plus monad/case simplification.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: E0072 sanitized-boundary attempt
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T081233Z_m1655_t001

#### Progress note
This replaces the failed raw-Resume argument-error simplification with a reusable boundary lemma whose statement contains no generated optional-driver premise.

#### Summary
- Add a local theorem near the existing ExtCall helper block in `vyperTypeStmtSoundnessScript.sml`.
- The lemma must not mention the generated optional-driver IH.
- It should prove that an `eval_exprs` error causes the ExtCall expression to return the same error/state immediately.
- The proof should use only `Once evaluate_def` and basic monad definitions/case reduction.
- If this probe times out or exposes the generated optional-driver prefix, stop and escalate; do not proceed to success branches.

#### Statement
Suggested theorem shape (exact variable names may follow the file):
```sml
Theorem eval_extcall_args_error[local]:
  eval_exprs cx es st = (INR y,args_st) ==>
  eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
    (INR y,args_st)
```
If `eval_expr` is syntactic sugar for the evaluator, use the file's existing spelling, but keep this exact semantic content.

#### Approach
Prove by `rw[]`/`strip_tac`, unfold `Once evaluate_def` for the `Call ... ExtCall ...` expression, then rewrite with the `eval_exprs` assumption and monad definitions already used in nearby call proofs (`bind_def`, `return_def`, `raise_def` if needed). Do not unfold later ExtCall operations; the branch should disappear before target/value/calldata code is visible.

#### Not to try
Do not run this as a partial Resume proof. Do not simplify with the optional-driver generated IH in context. Do not add a giant prefix adapter theorem. A proof longer than a few lines or a >4KiB goal is a plan failure.

### C0.3: Prove the argument-evaluation and place-expression halves of the ExtCall Resume
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Once C0.2 exists, the raw E0072 argument-error branch can be closed by a boundary lemma instead of simplification. The place-expression half is already ruled out by `type_place_expr_Call_ExtCall_NONE`. This is standard Resume orchestration.
- Dependencies: C0.2
- Supersedes: old C0.2 static/nonstatic leaves as initially scheduled proof work
- Progress transition: `replacement`
- Carries progress/evidence from: type_place_expr_Call_ExtCall_NONE, extcall_static_args_runtime_typed_dest, extcall_nonstatic_args_runtime_typed_dest

#### Progress note
This is not a resurrection of the old static/nonstatic leaves; it starts from the new C0.2 boundary and only then opens the success branch.

#### Summary
- Replace the `cheat` body of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` with a focused shell.
- Close the second conjunct/place-expression obligation immediately using `type_place_expr_Call_ExtCall_NONE`.
- Extract/name the expression-list IH and optional-driver IH, but do not apply the optional-driver IH yet.
- Split `eval_exprs cx es st`; apply the expression-list IH to obtain runtime consistency and `no_type_error_result` for arguments.
- If `args_res = INR y`, use C0.2 plus the IH result to close immediately.
- Continue only with `args_res = INL vs`.

#### Statement
Proof target:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:
  ...
QED
```
This component covers the Resume shell through isolation of the single argument-success path; it should leave no live argument-error or place-expression subgoal.

#### Approach
Follow the IntCall Resume pattern for naming generated IH assumptions, but do not `MATCH_MP_TAC` a monolithic helper against the raw goal. After one-step `well_typed_expr_def` and `evaluate_def`, immediately split `eval_exprs`. Use the expression-list IH with `env`, `st`, `args_res`, `args_st`; for the `INR` case rewrite the whole call result using `eval_extcall_args_error` and finish from the IH's `runtime_consistent`/`no_type_error_result` facts.

#### Not to try
Do not use `simp[no_type_error_result_def]` on the raw `args_res = INR y` Resume goal. Do not keep both argument-error and success paths active. Do not destruct generated names produced by broad `gvs[AllCaseEqs()]`.

### C0.4: Step through static and nonstatic ExtCall prefix branches up to external-call success
- Kind: `proof_branch`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The required runtime typing destructors and monadic preservation lemmas already exist locally. This is a careful linear split of concrete branches, closing all error exits immediately as non-TypeError/runtime-error cases.
- Dependencies: C0.3
- Supersedes: old C0.2, old C0.3
- Progress transition: `replacement`
- Carries progress/evidence from: extcall_static_args_runtime_typed_dest, extcall_nonstatic_args_runtime_typed_dest, run_ext_call_accounts_well_typed

#### Progress note
Prior static/nonstatic branch ideas may be reused only after the new argument-success boundary from C0.3 has been reached; their old scheduling without C0.2/C0.3 is invalidated.

#### Summary
- Work only in the single `INL vs` argument-success path.
- Split `is_static` once.
- Static branch: use `extcall_static_args_runtime_typed_dest` to obtain `dest_AddressV (HD vs) = SOME target_addr` and prove `vs <> []`.
- Nonstatic branch: use `extcall_nonstatic_args_runtime_typed_dest` to obtain target and amount, and prove `vs <> []` and `TL vs <> []`.
- Step linearly through target/value extraction, calldata build, account lookup, transient storage, `run_ext_call`, result tuple, and revert check.
- Close each failed operation branch immediately with monad definitions and `no_type_error_result_def`; keep only one success path alive.

#### Statement
This is an internal proof segment of `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`: after argument success, all prefix error branches before account/transient updates are discharged, leaving only external-call success/revert-success/update/return-continuation obligations.

#### Approach
Use local simplification lists like nearby Send/RawLog proofs but scoped to the single next operation: `bind_def`, `ignore_bind_def`, `check_def`/`assert_def`, `return_def`, `raise_def`, `lift_option_def`, `get_accounts_def`, `get_transient_storage_def`. Prefer `Cases_on` one operation at a time, followed by a small close of the error branch. For external-call success, derive `accounts_well_typed accounts'` with `run_ext_call_accounts_well_typed` before account updates.

#### Not to try
Do not unfold the entire ExtCall monadic prefix and then run `AllCaseEqs()`. Do not let static and nonstatic branches or multiple prefix failures remain in parallel. Do not specialize the optional-driver IH in this component; it is not needed before the return-data continuation.

### C0.5: Close the ExtCall success continuation and specialize optional-driver IH only at the final branch
- Kind: `proof_branch`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: Existing helpers are designed for this exact tail: `extcall_success_continuation_sound_cond_driver_ih` handles the final continuation with a conditional driver IH, and account/transient update preservation facts are already used by the helper. The only delicate point is to specialize the generated optional-driver IH after all concrete prefix facts are available.
- Dependencies: C0.4
- Checkpoint: yes
- Supersedes: old generated-prefix adapter approach
- Progress transition: `replacement`
- Carries progress/evidence from: extcall_success_continuation_sound_cond_driver_ih, extcall_after_state_update_tail_sound, extcall_return_tail_sound, E0072
- Invalidates prior progress/evidence: old broad generated-prefix adapter theorem strategy

#### Progress note
This component carries forward the existing tail helper lemmas but invalidates the old idea of recovering the driver premise from the top-level Resume context. The optional-driver IH is consumed only after branch facts establish the concrete success continuation.

#### Summary
- In the unique success path, after `run_ext_call` succeeds, split the result tuple and `success` check.
- For revert/failure branches, close immediately as non-TypeError runtime errors.
- After successful `update_accounts` and `update_transient`, call the existing continuation helper with a conditional driver IH.
- Specialize the generated optional-driver IH only if the branch has `returnData = [] /
IS_SOME drv`.
- Finish the expression result typing and runtime consistency obligations, then run `holbuild build vyperTypeStmtSoundnessTheory`.

#### Statement
Final proof segment for:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]
```
The completed Resume must remove the `cheat` at `vyperTypeStmtSoundnessScript.sml:17231` and build `vyperTypeStmtSoundnessTheory`.

#### Approach
Use `extcall_success_continuation_sound_cond_driver_ih` rather than the unconditioned `extcall_success_continuation_sound` if the generated optional-driver IH is guarded by prefix facts. Supply runtime consistency from the argument IH result plus account/transient update helper premises, well-formed return type from the typing branch, and `well_typed_opt env drv`/`!e. drv = SOME e ==> expr_type e = ret_type` from `well_typed_expr_def`. For the conditional driver premise, enter the `returnData = [] /
IS_SOME drv` subcase, then specialize the generated optional-driver IH with the concrete prefix facts already split in the current branch and pass the resulting ordinary IH to the continuation helper.

#### Not to try
Do not specialize the optional-driver IH at the top of the Resume. Do not prove a new long generated-prefix adapter theorem unless this component is escalated and the strategist explicitly reauthorizes it. Do not use broad simplification to recover hidden prefix premises. If applying the continuation helper requires manual theorem plumbing with a long `qspecl_then` list or ASSUME-quoted prefix facts, stop and escalate because the proof interface is wrong.

### C0.6: Verify, update task-local progress notes, and commit the ExtCall proof unsigned
- Kind: `integration_validation`
- Risk: 1
- Work priority: 50
- Work units: 2
- Rationale: Mechanical validation and handoff after the proof components build. The task explicitly requires progress commits and forbids GPG signing.
- Dependencies: C0.5
- Checkpoint: yes
- Supersedes: old C0.3 handoff as final state
- Progress transition: `replacement`
- Carries progress/evidence from: E0075

#### Progress note
The old unsigned stop/report commit remains historical evidence; this component creates the new proof-completion checkpoint if C0.5 succeeds.

#### Summary
- Run `holbuild build vyperTypeStmtSoundnessTheory` after removing the ExtCall_result cheat.
- Inspect `git diff -- semantics/prop` and `git status --short`.
- Update `TYPE_SYSTEM_REWRITE_PLAN.md`/state notes to record the completed ExtCall proof and any exact helper names introduced.
- Stage only intentional tracked files under `semantics/prop`.
- Commit with `git commit --no-gpg-sign`; never sign and never `git add -A`.

#### Statement
Integration deliverable: `vyperTypeStmtSoundnessTheory` builds with the `Expr_Call_ExtCall_result` cheat removed, task-local plan/state notes reflect the new proof status, and the changes are committed unsigned if there are tracked changes to commit.

#### Approach
Use the task's normal target build command. Treat a successful build as completion only for this C0 ExtCall branch, not for unrelated remaining cheats. If there are untracked scratch/legacy files, leave them untracked unless explicitly instructed otherwise.

#### Not to try
Do not commit files outside `semantics/prop`. Do not include failed proof experiments or generated logs. Do not claim final whole-repository soundness if other task-scoped components outside C0 remain.
