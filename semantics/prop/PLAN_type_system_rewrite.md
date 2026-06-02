# PLAN

## Structured Components

### C0: ExtCall proof-boundary gate for type-system rewrite
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: With C0.1 decomposed into Risk-1/2 branch-local leaves, the immediate C0 blocker is no longer a no-frontier high-risk gate. This record is included only as the required parent for dotted C0.1 components; siblings remain governed by their existing plan/dependencies and are not replanned here.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0205

#### Progress note
Parent risk/frontier status is repaired only to the extent needed for C0.1. No sibling progress is reclassified here.

#### Summary
Parent record included for dotted-component validity. This update only repairs C0.1, the static ExtCall success proof-boundary blocker from E0205. It does not authorize C0.2+ until scheduler/dependencies permit them after C0.1 progress. The C0.1 repair uses the maintainer-approved careful linear ExtCall proof shape and stays inside `semantics/prop`.

#### Argument
For the repaired C0.1 subtree, static ExtCall soundness proceeds by isolating prefix failures before the success continuation and handling the single successful external-call path through existing continuation lemmas. No evaluator definition changes are required.

#### Definition design
No definitions change. The proof interface is the existing local ExtCall helper block in `vyperTypeStmtSoundnessScript.sml`, especially `run_ext_call_accounts_well_typed` and `extcall_success_continuation_sound_cond_driver_ih`.

#### Code structure
All C0.1 edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`; do not edit outside `semantics/prop`. Commit progress with `git commit --no-gpg-sign`.

### C0.1: Linear static ExtCall success proof with branch-local driver IH
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: E0205 showed the old monolithic refactor was too risky, but the remaining work can be made standard by keeping one outer Resume, proving the three already-exposed prefix-error branches first, and using the existing ExtCall continuation/projection lemmas for the run-success branch. The only delicate point—optional-driver IH production—is constrained to a single concrete SOME/T success branch and is represented as a branch-local conditional assertion, not as top-level generated-prefix mining.
- Supersedes: C0.1@E0205
- Progress transition: `refinement`
- Carries progress/evidence from: E0199, E0205, TO_type_system_rewrite-20260601T220715Z_m4039_t001, TO_type_system_rewrite-20260601T220715Z_m4046_t001

#### Progress note
Carries forward the useful E0205 source state and build-clean partial refactor, but replaces the failed coarse Risk-2 assumption with explicit low-risk branch leaves. E0205 remains evidence for what not to try; it is not treated as proof completion.

#### Summary
- Stay inside `semantics/prop/vyperTypeStmtSoundnessScript.sml`; do not touch evaluator/semantics definitions or files outside `semantics/prop`.
- Preserve the kept E0205 refactor: `generated_driver_ih` mining is gone, and static calldata failure, empty-code failure, and `run_ext_call = NONE` are explicit Resume placeholders.
- Complete `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` branch-by-branch with only one live success path.
- Use existing local lemmas such as `extcall_static_args_runtime_typed_dest`, `extcall_static_args_runtime_typed_nonempty`, `run_ext_call_accounts_well_typed`, and especially `extcall_success_continuation_sound_cond_driver_ih` / `extcall_after_state_update_tail_sound` / `extcall_static_projected_sound` as proof boundaries.
- Produce the optional-driver IH only after the concrete run-success continuation branch has been isolated; do not reconstruct it from the top-level Resume context.
- This component supersedes the blocked coarse C0.1 refactor from E0205 and provides a low-risk frontier again.

#### Description
The source is currently build-clean only because the static ExtCall success Resume contains branch-local cheats. The strategy is not to introduce new nested success suspends (Finalise rejected those in E0205), but to keep the single existing `Expr_Call_ExtCall_result_static_success` Resume as the proof container. First discharge the three explicit prefix-error Resume placeholders. Then replace the inline run-success cheat in the same outer Resume by a linear proof: split `run_ext_call`, immediately close NONE/reverted/error outcomes, and on `SOME (T, returnData, accounts', tStorage')` use the continuation helper whose premise is a conditional driver IH.

#### Statement
Complete the static branch of:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]:
  ...
QED
```
and its current branch-local Resume placeholders:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_calldata_error]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_empty_code_error]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_run_none]: ... QED
```
No theorem statement changes are permitted.

#### Approach
Use a linear monadic proof boundary, not a generated-prefix abstraction. The proof should have exactly the current outer static-success Resume and no additional success-branch Resume labels unless a build probe first proves Finalise recognizes that label. For the final success branch, assert the conditional premise expected by `extcall_success_continuation_sound_cond_driver_ih`: `returnData = [] /\ IS_SOME drv ==> !env0 st0 res0 st0'. ...`; prove it only in the concrete `run_ext_call = SOME (T, returnData, accounts', tStorage')` branch by specializing the generated optional-driver IH with the already split prefix facts, then immediately pass that assertion to the continuation lemma.

#### Not to try
Do not revive `generated_driver_ih` as a top-level named mined assumption. Do not use broad `simp`/`gvs`, `AllCaseEqs()`, or a generated-prefix adapter theorem over the whole ExtCall prefix. Do not create nested success suspend labels such as `Expr_Call_ExtCall_static_run_success` or `Expr_Call_ExtCall_static_run_some` without first confirming Finalise accepts the placement; E0205 tried two such labels and both failed. Do not begin C0.2+ while this C0.1 proof remains cheated.

#### Argument
The static ExtCall proof has two independent layers. The prefix layer evaluates arguments, target extraction, calldata construction, code-presence check, transient/account retrieval, and `run_ext_call`; all failure branches return runtime errors or unchanged states, so type soundness follows by simple rewriting and the already-established typed argument facts. The success-continuation layer starts only after `run_ext_call` returns `SOME (T, returnData, accounts', tStorage')`: `run_ext_call_accounts_well_typed` gives `accounts_well_typed accounts'`, updating accounts/transient preserves runtime consistency via the existing update lemmas, and the return tail is handled by `extcall_success_continuation_sound_cond_driver_ih`. If `returnData = []` and `drv` is present, the generated optional-driver recursive premise is needed; otherwise ABI decoding plus `evaluate_abi_decode_return_well_typed` proves the returned value has `ret_type`. Thus the only generated IH use is branch-local and conditional, exactly matching the continuation lemma’s boundary.

#### Definition design
No definitions should change. The proof interface is the existing ExtCall helper block around lines 9460--10107. Treat `run_ext_call_accounts_well_typed` as the only fact needed about successful external calls. Treat `extcall_success_continuation_sound_cond_driver_ih` as the consumer boundary for the post-success monadic tail; it intentionally accepts a conditional driver IH so callers do not need to prove driver soundness unless `returnData = [] /\ IS_SOME drv`. Failure sign: if the executor is unfolding `run_ext_call_def`, `make_ext_call_state_def`, ABI internals, or the entire generated ExtCall prefix in the main Resume, the boundary is being bypassed and the session should stop.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep helper theorems in the existing local-helper area before the mutual proof; do not move them outside `semantics/prop`. The C0.1 leaves edit only the four static ExtCall Resume blocks around lines 17748--17789 and may use local lemmas already earlier in the same file. Build with `holbuild` for `vyperTypeStmtSoundnessTheory` after each leaf or after a small batch; commits must be made with `git commit --no-gpg-sign` when progress is committed.

### C0.1.1: Audit and preserve the build-clean static prefix refactor
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Mechanical source audit/cleanup only: the kept E0205 state already builds, and this leaf merely removes any stale failed success-suspend remnants while preserving the current explicit error placeholders and inline success cheat.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0205, TO_type_system_rewrite-20260601T220715Z_m4039_t001, TO_type_system_rewrite-20260601T220715Z_m4046_t001

#### Progress note
This leaf explicitly preserves the accepted partial refactor and stable build from E0205.

#### Summary
Confirm the source is in the intended C0.1 baseline before proof work. The static-success Resume should contain the linear prefix split, the three explicit branch-placeholder Resumes, and one inline run-success cheat. There should be no stale `generated_driver_ih` mining and no orphan success Resume labels from failed Finalise attempts. Verify `vyperTypeStmtSoundnessTheory` still builds if any cleanup is made.

#### Description
This is a guard against repeating E0205 failures. The executor should inspect only the ExtCall static-success area and remove stale labels/proof fragments such as `Expr_Call_ExtCall_static_run_success` or `Expr_Call_ExtCall_static_run_some` if they are still present in the working tree. Do not otherwise refactor the mutual proof.

#### Statement
No theorem statement; source-shape invariant for `semantics/prop/vyperTypeStmtSoundnessScript.sml` around `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`.

#### Approach
Run `git status`, inspect the local source around the four static ExtCall Resume blocks, and make the smallest cleanup needed to match the build-clean E0205 baseline. If the file is already in that shape, close this component with no edit. If edited, build `vyperTypeStmtSoundnessTheory`.

#### Not to try
Do not start proving the inline run-success cheat in this leaf. Do not add any new suspend/Resume label. Do not touch non-ExtCall proofs or files outside `semantics/prop`.

### C0.1.2: Discharge static ExtCall prefix-error placeholders
- Kind: `proof`
- Risk: 1
- Work priority: 10
- Work units: 3
- Rationale: These branches are already isolated and do not require the optional-driver IH. Each branch is a monadic failure path whose result is a runtime error or unchanged state, so rewriting with the monad/error definitions should close the type-soundness obligations mechanically.
- Dependencies: C0.1.1
- Progress transition: `refinement`
- Carries progress/evidence from: E0205

#### Progress note
E0205 exposed these branches and showed the source builds with cheats; this leaf turns that partial progress into real proofs.

#### Summary
Prove the three current cheated Resume placeholders: calldata construction failure, empty-code assertion failure, and `run_ext_call = NONE`. These are prefix failures before the success continuation, so no driver recursive premise is needed. Use only the branch-local assumptions produced by the outer static-success proof. Build after replacing the cheats.

#### Statement
Replace cheats in:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_calldata_error]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_empty_code_error]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_run_none]: ... QED
```

#### Approach
For each Resume, start with `RESUME_TAC`, expose the branch-local equality for the remaining monadic expression, and rewrite only the necessary monad/error definitions: `bind_def`, `return_def`, `raise_def`, `assert_def`, `check_def`, `get_accounts_def`, `get_transient_storage_def`, `no_type_error_result_def`, plus update defs only if present. The goal should reduce to inherited `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, and the fact that runtime errors are not type errors. Keep the branches separate; do not share a generated-prefix helper.

#### Not to try
Do not unfold the whole `evaluate_def` again in these Resume bodies; the outer Resume already isolated the branch. Do not use `AllCaseEqs()` or broad `gvs` over the whole prefix. Do not mention or specialize the optional-driver IH; these branches do not evaluate `drv`.

### C0.1.3: Prove branch-local conditional optional-driver IH in the concrete static run-success branch
- Kind: `proof_boundary`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This is the repaired proof interface for the E0205 blocker. It is low-risk because it is only a branch-local assertion after `run_ext_call = SOME (T, returnData, accounts', tStorage')` has been reached, matching the maintainer clarification and the premise shape of `extcall_success_continuation_sound_cond_driver_ih`. It avoids the failed top-level generated-prefix mining.
- Dependencies: C0.1.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0199, E0200, E0205

#### Progress note
This leaf keeps the useful branch isolation evidence from E0199/E0205 but changes the interface: generated IH use is local and conditional, not a named mined assumption or top-level reconstruction.

#### Summary
Inside the existing `Expr_Call_ExtCall_result_static_success` Resume, reach the concrete run-success continuation branch and locally assert the conditional driver IH needed by the continuation lemma. The assertion should have the exact shape required by `extcall_success_continuation_sound_cond_driver_ih`: it is guarded by `returnData = [] /\ IS_SOME drv`. Prove it by one branch-local specialization of the generated optional-driver premise using already split prefix facts. Leave other success-tail obligations to C0.1.4 if necessary.

#### Statement
Local assertion to establish in the run-success branch:
```hol
returnData = [] /\ IS_SOME drv ==>
  !env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\
    context_well_typed cx /\ accounts_well_typed st0.accounts /\
    functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
    (well_typed_expr env0 (THE drv) ==>
     state_well_typed st0' /\ env_consistent env0 cx st0' /\
     accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
     case res0 of
     | INL tv => expr_result_typed env0 (THE drv) tv
     | INR _ => T)
```

#### Approach
Do this only after the proof has split `run_ext_call ... = SOME (T, returnData, accounts', tStorage')` and has the prefix facts for argument evaluation, target, calldata, nonempty code, accounts, transient storage, tx params, success, updates, and `returnData` in context. Use the generated optional-driver premise once: specialize it with the concrete branch variables (the original `st`, `x`, `args_st`, target, calldata, accounts/tStorage, result tuple, etc.), discharge its prefix antecedent by the current branch equations, then introduce `env0 st0 res0 st0'` and the recursive-call assumptions. Keep the proof text local and linear; if a tactic would need a long top-level prefix reconstruction, stop and report stuck.

#### Not to try
Do not create a separate generated-prefix adapter theorem; that is explicitly forbidden. Do not try `asm "generated_driver_ih" irule`, broad `mp_tac >> simp[]`, `AllCaseEqs()`, or `gvs` over the whole generated prefix; E0200/E0205 showed these fail or time out. Do not suspend this success branch unless a small build probe first shows Finalise recognizes the label; previous success labels failed Finalise.

### C0.1.4: Close the static run-success continuation with existing ExtCall lemmas
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Once C0.1.3 supplies the conditional driver IH, the remaining success branch is a standard application of existing local continuation lemmas plus `run_ext_call_accounts_well_typed`; no new semantic argument is needed.
- Dependencies: C0.1.2, C0.1.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0205

#### Progress note
Builds on the E0205 branch split but replaces the failed local continuation attempt with the existing continuation-boundary lemmas and the explicit C0.1.3 conditional IH.

#### Summary
Replace the inline run-success cheat in `Expr_Call_ExtCall_result_static_success`. Split the `SOME` result tuple, close reverted/error subcases immediately, prove `accounts_well_typed accounts'` from `run_ext_call_accounts_well_typed`, establish `runtime_consistent env cx args_st`, and invoke `extcall_success_continuation_sound_cond_driver_ih` or `extcall_after_state_update_tail_sound` with the branch-local conditional driver IH. Build `vyperTypeStmtSoundnessTheory` with no cheats in the static-success branch.

#### Statement
Remove the inline cheat after:
```sml
Cases_on `run_ext_call cx.txn.target target_addr x' NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)`
```
in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`, completing the `SOME (T, returnData, accounts', tStorage')` branch and all immediate failure subcases.

#### Approach
Keep the proof inside the existing outer Resume. After `Cases_on run_ext_call`, use lightweight tuple splitting (`PairCases_on` or targeted `Cases_on result`) and avoid simplifying unrelated prefix assumptions. For `SOME (T, returnData, accounts', tStorage')`, derive `accounts_well_typed accounts'` with `drule_all run_ext_call_accounts_well_typed`, derive `runtime_consistent env cx args_st` from the inherited state/env/account facts, then `irule`/`drule_all` the continuation helper and supply the conditional driver IH from C0.1.3. The final expression-typed conclusion should be discharged by the helper, not by unfolding ABI decoding or driver evaluation in the main proof.

#### Not to try
Do not use `gvs[return_def, raise_def]` on a goal with ten generated prefix subgoals; E0205 timed out there. Do not unfold `run_ext_call_def`, ABI decoding, or update/runtime definitions except through the listed helper lemmas. Do not add a new success Resume label as the primary plan; Finalise failures are evidence that this proof should stay inline in the existing Resume.

### C0.2: Close static ExtCall prefix error branches
- Kind: `proof`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: These branches are mechanical simplifications of the evaluator prefix after C0.1 exposes them: calldata construction failure, empty target code assertion failure, and `run_ext_call = NONE`/revert-like immediate error branches do not depend on the optional-driver IH.
- Dependencies: C0.1
- Carries progress/evidence from: E0199

#### Progress note
E0199 showed the static branch can be isolated; this leaf closes only the easy prefix branches.

#### Summary
- Prove the static ExtCall branches before the successful post-call continuation.
- Use `extcall_static_args_runtime_typed_dest` and `extcall_static_args_runtime_typed_nonempty` once after argument success.
- For each prefix failure, rewrite only the current monadic operation and close `no_type_error_result`, state/env/account preservation, and vacuous result typing.
- Keep only one active branch at a time.

#### Statement
Close the branch-specific suspends introduced by C0.1 for static ExtCall prefix errors/failures in `eval_all_type_sound_mutual[Expr_Call_ExtCall_result...]`.

#### Approach
Use the existing local proof text through `build_ext_calldata`, `NULL (lookup_account target_addr args_st.accounts).code`, and `run_ext_call`. After each case split, immediately rewrite `bind_def`, `return_def`, `raise_def`, `assert_def`, `get_accounts_def`, `get_transient_storage_def`, and `no_type_error_result_def` for that branch only. Preservation facts come from the argument IH state `args_st` or from operation helpers such as `run_ext_call_accounts_well_typed` where the branch has a concrete successful run.

#### Not to try
Do not continue case-splitting past a failure branch before closing it. Do not run global `gvs[..., AllCaseEqs()]` over the entire ExtCall prefix.

### C0.3: Prove static ExtCall success continuation without optional driver
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The existing helper `extcall_after_state_update_tail_sound_cond_driver_ih` is already tailored to the post-update tail. When `returnData <> []` or `drv = NONE`, its driver-IH premise is discharged vacuously and the remaining proof is standard runtime-consistency/account preservation plumbing.
- Dependencies: C0.1, C0.2

#### Summary
- Prove static ExtCall successful `run_ext_call` branches where the final continuation decodes ABI return data or has no driver.
- Establish `runtime_consistent env cx args_st`, updated accounts typing, and `get_tenv cx = env.type_defs`.
- Apply `extcall_after_state_update_tail_sound_cond_driver_ih` or `extcall_success_continuation_sound` with the driver premise vacuous.
- Reuse `run_ext_call_accounts_well_typed`, `runtime_consistent_get_tenv`, and `update_accounts_transient_runtime_consistent`.

#### Statement
Close the branch-specific static ExtCall success-tail suspend(s) with condition `~(returnData = [] /\ IS_SOME drv)` after successful `run_ext_call`.

#### Approach
After destructing `result` to obtain success, returned data, updated accounts, and updated transient storage, prove the runtime/account facts before touching the tail. Then invoke the existing tail helper with `qexistsl` for the concrete updated accounts, base state, return data, and result-success flag. The implication premise for the optional driver should be closed by contradiction from the branch condition.

#### Not to try
Do not unfold `evaluate_abi_decode_return` in the main ExtCall proof unless the tail helper cannot match. Do not manually repeat the body of `extcall_after_state_update_tail_sound_cond_driver_ih`; fix the helper invocation instead.

### C0.4: Prove static ExtCall optional-driver continuation at branch-local IH point
- Kind: `proof_checkpoint`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: This is the former blocker, but the new leaf is narrower than E0200: it must be attempted only after C0.1 has moved the suspend to the exact success continuation where `returnData = []`, `drv = SOME e`, the updated state, and the concrete driver evaluation are all in the goal. The allowed proof is a direct use of the native recursive IH in that local context, not reconstruction of a compact premise from the whole generated prefix.
- Dependencies: C0.1, C0.2
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0199, E0200
- Invalidates prior progress/evidence: old compact static_driver_ih producer obligation

#### Progress note
This replaces the old failed obligation with a branch-local checkpoint. E0200 remains evidence for what not to try; it does not count as proof progress for this new leaf.

#### Summary
- Close the static ExtCall success branch where `returnData = []` and `drv = SOME e`.
- First establish the updated state is runtime-consistent and accounts-well-typed.
- Derive `well_typed_expr env e` from `well_typed_opt env drv` and `drv = SOME e`.
- Specialize the native recursive IH only after the concrete `eval_expr cx e updated_st = (res,st')` assumption is visible.
- Feed that branch-local IH to `extcall_after_state_update_tail_sound_cond_driver_ih`/`extcall_success_continuation_sound`.

#### Statement
Close the branch-specific static ExtCall optional-driver suspend introduced by C0.1, at the concrete branch `returnData = [] /\ drv = SOME e`.

#### Approach
Do not try to manufacture a general compact IH theorem. In the branch, set `driver_st = args_st with <| accounts := accounts'; tStorage := tStorage' |>` (or the exact updated-state expression in the goal), prove `env_consistent env cx driver_st`, `state_well_typed driver_st`, `context_well_typed cx`, `accounts_well_typed driver_st.accounts`, and `functions_well_typed cx`, then specialize the native recursive IH for `eval_expr cx e driver_st = (res,st')`. Once it returns the usual expression invariant for `e`, use `extcall_after_state_update_tail_sound_cond_driver_ih`; if the only available IH still requires a long generated ExtCall prefix rather than the concrete driver evaluation premise, stop and escalate with that exact goal as evidence.

#### Not to try
Do not use `asm "generated_driver_ih" irule`, copied full assumptions, `MATCH_MP`/`CONJ` theorem plumbing, or exact-prefix forward chaining. Do not run `mp_tac >> simp[]` on the huge generated premise. Those were E0200 failures and maintainer-forbidden.

### C0.5: Prove nonstatic ExtCall result branch linearly
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The nonstatic branch should follow the same linear ExtCall structure as the static branch but without the static driver-tail blocker. It is currently cheated, so it is task-required, but no prior evidence identifies a proof-interface mismatch there.
- Dependencies: C0.1, C0.2, C0.3, C0.4

#### Summary
- Replace `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]: cheat` with a linear proof.
- Reuse the argument-evaluation IH and ExtCall argument runtime-typing destructors appropriate for the nonstatic case.
- Step through the nonstatic evaluator prefix one monadic operation at a time.
- Close transfer/run/update error branches immediately; use the existing ExtCall success-tail helper for the final continuation.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` without `cheat`.

#### Approach
Mirror the static proof discipline: rewrite `Once evaluate_def` only far enough to expose the next monadic operation, split it, and close that branch before proceeding. For successful external execution, prove runtime consistency and account typing before invoking the existing tail helper. If the nonstatic branch also reaches an optional driver continuation, reuse the C0.4 branch-local IH pattern after all prefix operations are discharged.

#### Not to try
Do not copy the static generated-prefix mining attempt. Do not leave both static and nonstatic success paths active in the same tactic state.

### C0.6: Prove RawCallTarget result branch
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: This is a remaining explicit cheat in the same statement-soundness theory. The neighboring Send, RawLog, and RawRevert branches demonstrate the intended local proof pattern, making this a standard branch proof once ExtCall no longer blocks the mutual theorem.
- Dependencies: C0.5

#### Summary
- Replace `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]: cheat` with a direct branch proof.
- Use the same shape as Send/RawLog/RawRevert: type-rule inversion, argument evaluation IH, argument runtime-typing destructors, operation split, no-TypeError/preservation helper, result-typing close.
- Add a small local RawCallTarget helper only if its conclusion exactly matches the operation success/error branch.
- Keep proof local to `vyperTypeStmtSoundnessScript.sml`.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` without `cheat`.

#### Approach
Invert `well_typed_expr env (Call _ RawCallTarget _ _)` with `Once well_typed_expr_def`, step through `Once evaluate_def`, and split `eval_exprs` first. On argument success, destruct the `exprs_runtime_typed` fact with existing raw-call argument typing lemmas if present; otherwise add one small local destructor matching the well-typed RawCallTarget argument list. For each raw-call operation result, use operation no-TypeError/preservation facts and prove the successful returned value satisfies `expr_result_typed` for the call expression.

#### Not to try
Do not introduce a broad raw-call soundness framework or edit raw-call semantics. Do not prove unrelated raw builtin branches unless the RawCallTarget proof directly depends on a small local helper.

### C0.7: Task-scoped final no-cheat build/audit and plan-state update
- Kind: `validation`
- Risk: 1
- Work priority: 60
- Work units: 2
- Rationale: After the proof leaves close, validation is mechanical: build the target theory, grep for remaining task-scoped cheats/suspends in the affected proof blocks, update task memory, and commit without GPG signing if committing is part of the session.
- Dependencies: C0.6
- Checkpoint: yes
- Carries progress/evidence from: E0201

#### Progress note
E0201 established a stable cheated baseline; this leaf verifies that the intentional local cheats have now been removed rather than merely relocated.

#### Summary
- Run the task-scoped build for `vyperTypeStmtSoundnessTheory` and any required final target named in the current plan.
- Grep/audit `semantics/prop/vyperTypeStmtSoundnessScript.sml` for remaining `cheat` in the C0-owned proof blocks.
- Update `PLAN_type_system_rewrite.md`, `STATE_type_system_rewrite.md`, and learnings to record completion and any branch helper additions.
- If making a commit, use `git commit --no-gpg-sign`; do not stage unrelated untracked artifacts.

#### Statement
Validation obligation: the task-scoped type-system rewrite proof has no remaining C0-owned cheats and the relevant HOL theory builds.

#### Approach
Use `holbuild` on `vyperTypeStmtSoundnessTheory` first. If the larger plan requires a final public theory build, run it only after the statement-soundness build passes. Audit by targeted grep around `Expr_Call_ExtCall_result`, `Expr_Call_ExtCall_result_nonstatic`, and `Expr_Call_RawCallTarget`; if unrelated repository cheats appear outside C0 scope, record them as notes rather than expanding this component.

#### Not to try
Do not treat a successful build with remaining local `cheat` as completion. Do not edit or stage files outside `semantics/prop`; do not GPG-sign commits.
