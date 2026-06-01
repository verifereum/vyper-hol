# PLAN

## Structured Components

### C0: Prove the ExtCall result branch of mutual expression type soundness under the narrowed maintainer authorization
- Kind: `proof_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The E0079 risk is addressed locally by replacing C0.3's failed equality-boundary consumer with a postcondition-shaped helper. Existing completed C0.2 and planned C0.4-C0.6 strategy remain valid; no unprovability or broader design conflict was found.
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

### C0.3: Close the ExtCall argument-error and place-expression shell via a postcondition-shaped boundary
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The prior equality-boundary consumer approach is blocked by E0079, but the mathematical branch is simple: when `eval_exprs` returns `INR`, the ExtCall evaluator returns the same error and state, and the expression-list IH supplies the postcondition. A helper whose conclusion is the branch postcondition avoids simplifier traversal of the generated optional-driver prefix.
- Dependencies: C0.2
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2, E0079
- Invalidates prior progress/evidence: C0.3-direct-equality-consumer

#### Progress note
E0079 validly invalidates the old C0.3 consumer interface, but also identifies the repair: keep C0.2 and replace only the raw Resume simplification bridge with a postcondition-shaped helper.

#### Summary
- Replace the failed direct use of `eval_extcall_args_error` in the raw Resume proof.
- Add one local helper with the exact result-postcondition conclusion needed for the `eval_exprs = INR` branch.
- Use the expression-list IH with `drule_all_then assume_tac`; do not discharge IH antecedents by `simp`.
- Complete the second/place-expression half by contradiction with `type_place_expr_Call_ExtCall_NONE`.
- This keeps the maintainer-approved linear ExtCall strategy intact and leaves C0.4/C0.5 blocked only until this shell is rebuilt.

#### Description
C0.3 no longer asks the executor to bridge an evaluator equality to a large generated Resume goal by simplification. The only allowed bridge is a helper outside the Resume context that consumes the argument-error evaluation equation, the original call evaluation equation, and the already-derived expression-list postcondition, then returns the exact expression-result postcondition for the ExtCall call.

#### Approach
First prove the helper in the local ExtCall helper section near `eval_extcall_args_error`. Then edit `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`: unfold only enough to split `eval_exprs`; in the `INR y` branch obtain the expression-list IH conclusion with `drule_all_then assume_tac`, and close by `irule`/`drule` of the helper. Finish the place-expression conjunct with `type_place_expr_Call_ExtCall_NONE`, without unfolding the ExtCall evaluator.

#### Not to try
Do not use `simp[eval_extcall_args_error]`, `gvs[eval_extcall_args_error]`, `simp[]` after `mp_tac` of the full call evaluation equation, `AllCaseEqs()`, or broad simplification over the generated optional-driver premise. E0079 shows even minimal-looking `simp[]` traverses the >4KiB generated prefix. Do not invent a long generated-prefix adapter theorem; the maintainer clarification forbids that architecture.

#### Argument
The argument-error branch is independent of every later ExtCall prefix operation. The evaluator first evaluates `es`; if that returns `INR y,args_st`, `eval_extcall_args_error` states the whole call evaluates to `(INR y,args_st)`. The expression-list IH gives `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, and `no_type_error_result (INR y)`. Substituting the call result equality gives exactly the expression-result postcondition; the result-typed subcase is vacuous for `INR`. The place-expression half is not an evaluator property: ExtCall calls have no place type by `type_place_expr_Call_ExtCall_NONE`.

#### Definition design
The key interface is a consumer boundary, not another evaluator expansion lemma. `eval_extcall_args_error` remains the computation boundary; the new helper is the proof-consumer boundary. Its conclusion should be the exact postcondition the Resume branch needs, so the Resume proof can use `irule` and assumption matching instead of simplifier search. Failure sign: if the helper or consumer proof mentions the generated optional-driver premise or unfolds the success prefix, the boundary is still too weak.

#### Code structure
Keep all changes inside `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place the new local helper immediately after `eval_extcall_args_error` or adjacent to the other ExtCall local helpers. The Resume proof remains at `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`; do not edit evaluator/semantics definitions. Commit only after `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)` succeeds, unsigned.

### C0.3.1: Add `eval_extcall_args_error_sound` as the postcondition-shaped argument-error helper
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: The helper is a direct consequence of C0.2 plus substitution. It is outside the generated Resume context, so no generated optional-driver prefix is present.
- Dependencies: C0.2
- Carries progress/evidence from: C0.2, E0079

#### Progress note
This is the consumer-shaped replacement for the failed equality-only interface observed in E0079.

#### Summary
- Prove a local helper immediately after `eval_extcall_args_error`.
- The helper consumes the argument-error `eval_exprs` equation, the original call `eval_expr` equation, and the expression-list IH postcondition for `(INR y,args_st)`.
- Its conclusion is exactly the expression-result postcondition needed by C0.3.2.
- It must not unfold the full ExtCall evaluator; use `eval_extcall_args_error` as the only computation fact.

#### Statement
Suggested local theorem shape:
```sml
Theorem eval_extcall_args_error_sound[local]:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ no_type_error_result (INR y) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
```
If the live goal uses constructor fields in a slightly different variable order, keep the conclusion shape and adjust quantifier order only.

#### Approach
Specialize/drule `eval_extcall_args_error` on the `eval_exprs` assumption to obtain the call evaluation equality `(INR y,args_st)`. Combine it with the supplied original call evaluation equation to rewrite/substitute `res = INR y` and `st' = args_st`. The remaining conjuncts are exactly assumptions; the `INL` result-typed branch is impossible after substitution.

#### Not to try
Do not prove this by unfolding `Once evaluate_def`; that would duplicate C0.2 and risk reintroducing monadic prefix simplification. Do not include the expression-list IH itself as a quantified implication in this helper; pass only its already-derived postcondition conjuncts so the consumer can avoid antecedent simplification.

### C0.3.2: Rewrite the `Expr_Call_ExtCall_result` Resume shell to use the postcondition helper and close the no-place half
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The remaining work is standard Resume proof editing provided the executor avoids whole-goal simplification. The argument-error branch closes by matching assumptions into C0.3.1, and the place-expression half closes by the existing no-place lemma.
- Dependencies: C0.3.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0079
- Invalidates prior progress/evidence: C0.3-direct-equality-consumer

#### Progress note
This leaf carries forward the live facts learned in E0079: `drule_all_then assume_tac` is acceptable for the expression-list IH, but any simplifier bridge from equality to postcondition is invalidated.

#### Summary
- Replace the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` only for the shell covered by C0.3.
- For the first/result conjunct, split just to the `eval_exprs` result.
- In the `INR y,args_st` branch, derive the expression-list IH conclusion by `drule_all_then assume_tac`, then `irule eval_extcall_args_error_sound`.
- Leave later successful ExtCall prefix/success-continuation work to C0.4 and C0.5; if the proof cannot be partitioned that way, stop and escalate.
- For the second/place conjunct, use `type_place_expr_Call_ExtCall_NONE` to contradict `type_place_expr ... = SOME vt`.

#### Statement
Target obligation is the existing suspended theorem:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:
  ...
QED
```
C0.3.2 is complete only when the argument-error branch and the place-expression half no longer contain cheats and `vyperTypeStmtSoundnessTheory` builds. Success/non-error ExtCall branches remain for C0.4/C0.5 only if the Resume proof structure explicitly leaves them as planned downstream work; otherwise escalate before committing.

#### Approach
Use the same initial destructuring as the prior attempt up to `Cases_on eval_exprs cx es st`. Instantiate the generated expression-list IH with `drule_all_then assume_tac` against the live assumptions; do not `qspecl_then ... mp_tac >> simp[]`. In the `INR` branch, preserve the original call evaluation assumption and apply `eval_extcall_args_error_sound` with the IH-derived `state/env/accounts/no_type_error` facts. For the place-expression conjunct, move the `type_place_expr ... = SOME vt` premise and rewrite with `type_place_expr_Call_ExtCall_NONE`.

#### Not to try
Do not `mp_tac` the full call eval equation and follow with `simp[]`; E0079 shows that still traverses the optional-driver prefix. Do not try to delete generated universal assumptions one by one until `simp[]` becomes fast; that is brittle and was already ineffective. Do not specialize the optional-driver IH in this component; that belongs only to the final success continuation in C0.5.

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
