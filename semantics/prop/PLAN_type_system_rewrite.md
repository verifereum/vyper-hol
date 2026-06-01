# PLAN

## Structured Components

### C0: Prove the ExtCall result branch of mutual expression type soundness under the narrowed maintainer authorization
- Kind: `proof_subtree`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.3.2 risk 3. C0.3.2's planned Resume shell still requires a bridge from the generated evaluator equation/postcondition helper to the raw Resume goal while the generated optional-driver prefix remains live. Both direct `irule` and specialized helper application led either to wrong conjunct focus or simplifier timeout; the component is not a straightforward Risk-2 proof as stated.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.1, C0.2, E0079

#### Progress note
C0 remains the same top-level ExtCall branch obligation. E0079 is accepted as local proof-interface evidence and repaired by refining C0.3, not by changing the overall C0 strategy.

#### Summary
- Continue the task-scoped ExtCall proof under the maintainer clarification.
- C0.2's computation boundary `eval_extcall_args_error` remains valid and committed.
- C0.3 is repaired by adding a consumer-shaped helper so the Resume proof avoids broad simplification over the generated optional-driver prefix.
- Downstream C0.4/C0.5 remain the linear branch-by-branch ExtCall success proof and final optional-driver IH use.
- All edits stay in `semantics/prop`; evaluator definitions are not changed.

#### Argument
The ExtCall proof is decomposed by the evaluator's monadic order. First close the argument-evaluation error branch: if `eval_exprs` returns `INR`, the whole ExtCall call returns that error and state, so expression-list IH postconditions transfer directly. Then handle concrete success-prefix operations linearly, closing each runtime-error exit immediately and preserving runtime consistency through account/transient updates. Only after reaching the single final success continuation may the optional-driver IH be specialized.

#### Definition design
Use local proof boundaries rather than generated-prefix adapters. Computation facts such as `eval_extcall_args_error` should be proved outside the huge Resume context. Consumer branches inside the Resume should call helpers whose conclusions match the postcondition, using `irule`/`drule` and selected assumptions. Failure sign: any proof step that needs `simp`/`gvs` over the full ExtCall prefix or generated optional-driver premise must stop and be refactored into a smaller boundary lemma.

#### Code structure
All changes go in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and task-local markdown files only. Local ExtCall helpers belong near the existing ExtCall helper block around `eval_extcall_args_error`; the suspended Resume remains at `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`. Validate with `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)` and make unsigned commits only.

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

### C0.3: Close the ExtCall argument-error and place-expression shell using conjunct-specific boundaries
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The previous full-postcondition helper is valid but too coarse for the raw Resume context. Splitting it into conjunct-specific lemmas whose conclusions exactly match already-split goals removes the need for `simp[]`, `gvs[]`, or an implication bridge under the generated optional-driver prefix. The remaining Resume shell is a standard branch split plus `irule`/`first_assum ACCEPT_TAC` against small local lemmas.
- Dependencies: C0.2
- Supersedes: C0.3@old, C0.3.2@old
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2, C0.3.1, E0080, E0081
- Invalidates prior progress/evidence: C0.3.2@old

#### Progress note
C0.2/C0.3.1 remain valid progress. E0081 is accepted as risk-mismatch evidence and invalidates only the old full-postcondition-in-Resume application strategy. The mathematical obligation is unchanged; the helper interface is refined to match split subgoals.

#### Summary
- Keep the committed `eval_extcall_args_error_sound` progress, but stop trying to apply it directly in the generated Resume context.
- Add small local conjunct-specific argument-error lemmas outside the Resume proof; each lemma should conclude one final conjunct such as `state_well_typed st'` or `env_consistent env cx st'`.
- Rewrite only the `Expr_Call_ExtCall_result` shell enough to split the argument evaluation result, close `INR y` by these lemmas, and close the place-expression half using `type_place_expr_Call_ExtCall_NONE`.
- The invariant is: if `eval_exprs cx es st = (INR y,args_st)`, then the whole ExtCall call returns immediately with the same error/result state, so all postconditions are inherited from the expression-list IH fact for `(INR y,args_st)`.
- Do not simplify the generated optional-driver prefix in this component.

#### Description
This subtree repairs the C0.3.2 risk mismatch from E0081 by changing the proof interface, not by asking for a cleverer tactic. The raw Resume context has already split final postcondition conjuncts and contains a large generated optional-driver success-prefix implication. Therefore helper conclusions must match live conjunct goals directly and their hypotheses must be assumptions available after the expression-list IH has been applied.

#### Not to try
Do not apply `eval_extcall_args_error_sound` directly in the raw branch; E0081 showed `irule` misses after conjunct splitting and specialized application still needs a timeout-prone bridge. Do not discharge helper antecedents with `simp[]`, `gvs[]`, `rpt conj_tac >> first_assum ACCEPT_TAC` under the generated prefix, or broad case cleanup over the optional-driver success prefix. Do not split into success-prefix ExtCall operations in C0.3; that belongs to C0.4 after the argument-error shell is closed.

#### Argument
For the argument-error branch, the evaluator semantics of ExtCall are simple: the first operation is `eval_exprs cx es st`; if it returns `(INR y,args_st)`, the surrounding `Call ... ExtCall ...` returns exactly `(INR y,args_st)` without executing any target/value/calldata/accounts/driver prefix. C0.2 proved this equality as `eval_extcall_args_error`, and C0.3.1 packaged the full soundness postcondition outside the hostile Resume context. E0081 shows the full package is still too coarse once the Resume goal has split conjuncts. The repaired argument proves projections of the same substitution fact: from the argument-error evaluator equality and the already-derived expression-list IH postconditions for `(INR y,args_st)`, derive each conjunct about `st'`/`res` separately. In the Resume branch, first use the expression-list generated IH with `drule_all_then assume_tac` to obtain facts about `args_st` and `INR y`; then, after `Cases_on args_res`, use conjunct-specific helpers in the `INR y` branch. For the place-expression half, `type_place_expr_Call_ExtCall_NONE` makes the premise `type_place_expr ... = SOME vt` contradictory, so it should be closed without entering the ExtCall evaluator prefix.

#### Definition design
No semantic definitions should change. The proof-interface boundary is a family of local lemmas that project the argument-error substitution fact into already-split postconditions. Each lemma should have a conclusion that is a single common Resume subgoal and hypotheses that are plain assumptions, not an implication to be simplified. Failure signs: any proof step in the Resume branch that invokes `simp[]`, `gvs[]`, `AllCaseEqs()`, or unfolds `evaluate_def` after the argument-error branch is selected is recreating E0081; stop and adjust the helper statement instead.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place the new conjunct-specific lemmas immediately after `eval_extcall_args_error_sound` so they can reuse C0.2/C0.3.1 and stay outside the generated Resume context. Keep the current intentional `cheat` baseline for `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` until the new helper lemmas build. Then replace only that Resume body. Do not edit evaluator/semantics files or files outside `semantics/prop`. Commit successful progress unsigned.

### C0.3.1: Keep `eval_extcall_args_error_sound` as the full postcondition boundary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This helper was proved and committed in E0080/commit 0c29945fa. It remains useful as evidence and optionally as a source theorem for projections, but the Resume proof must not apply it directly under the generated prefix.
- Dependencies: C0.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0080, C0.3.1, commit:0c29945fa

#### Progress note
The proven helper remains correct and committed; only its downstream use strategy changes.

#### Summary
- Carry forward the existing local theorem `eval_extcall_args_error_sound`.
- It is valid stable progress and should not be reproved unless the source no longer contains it.
- Downstream helpers may use either this theorem or directly use `eval_extcall_args_error`.
- Its role is now proof infrastructure outside the raw Resume context, not the direct consumer lemma for split subgoals.

#### Statement
Existing local theorem:
```sml
Theorem eval_extcall_args_error_sound[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ no_type_error_result (INR y) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
```

#### Approach
No new executor work unless the file does not contain the theorem. Treat this component as carried-forward infrastructure. If projections use this theorem, derive them outside the Resume proof by `drule`/`strip_tac` and then `gvs[]` only in the small lemma proof, not in the Resume branch.

#### Not to try
Do not apply this theorem directly in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`; E0081 showed that the live subgoal is usually a single conjunct and the generated prefix makes implication bridging timeout-prone.

### C0.3.2: Add conjunct-specific ExtCall argument-error projection helpers
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Each lemma is a direct projection of C0.2/C0.3.1 and is proved outside the generated Resume context. The statements are intentionally small and match split goals, so their consumer use requires only `irule` plus existing assumptions.
- Dependencies: C0.3.1
- Checkpoint: yes
- Supersedes: C0.3.2@old
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2, C0.3.1, E0081
- Invalidates prior progress/evidence: C0.3.2@old

#### Progress note
Replaces the old Resume-shell leaf with a lower-risk helper interface. E0081 is used as evidence that split-conjunct helper conclusions are required.

#### Summary
- Prove local projection lemmas for the `INR y` argument-error branch.
- Conclusions should separately cover `state_well_typed st'`, `env_consistent env cx st'`, `accounts_well_typed st'.accounts`, `no_type_error_result res`, and the expression-result typing case.
- Hypotheses should be plain live assumptions after applying the expression-list IH: `eval_exprs ... = (INR y,args_st)`, the whole-call eval equation, and the relevant inherited postcondition fact about `args_st`/`INR y`.
- These lemmas must not mention the generated optional-driver success prefix.
- Build after adding them before touching the Resume proof.

#### Statement
Add local lemmas of this shape (names may vary, but conclusions should remain conjunct-specific):
```sml
Theorem eval_extcall_args_error_state_well_typed[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    state_well_typed args_st ==>
    state_well_typed st'

Theorem eval_extcall_args_error_env_consistent[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    env_consistent env cx args_st ==>
    env_consistent env cx st'

Theorem eval_extcall_args_error_accounts_well_typed[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    accounts_well_typed args_st.accounts ==>
    accounts_well_typed st'.accounts

Theorem eval_extcall_args_error_no_type_error[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    no_type_error_result (INR y) ==>
    no_type_error_result res

Theorem eval_extcall_args_error_expr_result_typed[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') ==>
    (case res of
     | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
     | INR _ => T)
```

#### Approach
Prove each lemma outside the Resume context by `rpt strip_tac`, deriving `eval_expr cx (Call ...) st = (INR y,args_st)` from `eval_extcall_args_error`, then using the assumed whole-call eval equation to identify `res` and `st'`. It is acceptable to use `gvs[]` or project `eval_extcall_args_error_sound` inside these tiny lemmas because no generated optional-driver prefix is present. Keep the theorem statements conjunct-specific; do not combine them into one conjunction for the Resume consumer.

#### Not to try
Do not add a new implication-shaped helper with the full postcondition conclusion; that repeats C0.3.1 and fails at the consumer. Do not require `context_well_typed`, `functions_well_typed`, or well-typed-call premises in these projections unless HOL forces them; they are irrelevant to the immediate return substitution and make the consumer antecedent heavier.

### C0.3.3: Rewrite the ExtCall Resume shell to consume only projection helpers and close the no-place half
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Once the projection lemmas exist, the raw Resume proof no longer needs to apply a full postcondition theorem or simplify a generated implication. The executor only has to preserve the eval equation, obtain the expression-list IH facts with the known `drule_all_then assume_tac` pattern, split `args_res`, and close each `INR y` conjunct by a matching projection lemma.
- Dependencies: C0.3.2
- Checkpoint: yes
- Supersedes: C0.3.2@old
- Carries progress/evidence from: E0081
- Invalidates prior progress/evidence: C0.3.2@old

#### Progress note
This is the repaired consumer leaf. Prior attempts do not count as proof progress, but their failure evidence determines the no-simplifier consumer discipline.

#### Summary
- Replace the `cheat` body of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` only after C0.3.2 builds.
- In the first/well-typed-expression half, unfold the evaluator just enough to split `eval_exprs cx es st` and bind `args_res,args_st`, preserving the whole-call eval equation as an assumption.
- Use `drule_all_then assume_tac` for the expression-list IH; do not discharge its antecedent with `simp[]`.
- In the `args_res = INR y` branch, close each split conjunct with the corresponding C0.3.2 projection lemma.
- In the place-expression half, use `type_place_expr_Call_ExtCall_NONE` to contradict `type_place_expr ... = SOME vt` without traversing the ExtCall evaluator prefix.

#### Statement
Complete the existing suspended proof:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:
  ...
QED
```
No theorem statement changes are allowed.

#### Approach
Start from the clean cheat baseline. For the first conjunct, after rewriting `well_typed_expr_def` and one-step evaluator unfolding, immediately bind `eval_exprs cx es st = (args_res,args_st)` and apply the generated expression-list IH using `drule_all_then assume_tac` so facts about `args_st` are assumptions. Split `args_res`; leave the `INL vs` success path to C0.4 if the existing shell permits a `cheat`/suspend boundary, but for the `INR y` branch use only `irule eval_extcall_args_error_state_well_typed`, `..._env_consistent`, `..._accounts_well_typed`, `..._no_type_error`, and `..._expr_result_typed`, followed by `first_assum ACCEPT_TAC`/simple assumption selection. For the second conjunct, move the `type_place_expr ... = SOME vt` premise, rewrite with `type_place_expr_Call_ExtCall_NONE`, and close by contradiction before unfolding the evaluator.

#### Not to try
Do not use `simp[]` as a bridge after specializing a helper theorem; that is exactly the E0081 timeout. Do not apply `eval_extcall_args_error_sound` directly in this Resume branch. Do not call `AllCaseEqs()` or broad `gvs[evaluate_def,...]` over the success prefix. Do not specialize the optional-driver IH here; it is only for the concrete success continuation in C0.5 after C0.4 has discharged the prefix operations.

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
