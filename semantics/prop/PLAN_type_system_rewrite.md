# PLAN

## Structured Components

### C0: Task-scoped type-system rewrite context
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Validation parent only for the scoped subtree replacement. Its previous high risk was inherited from C0.5.4.5.1.2; this update supplies low-risk children for that blocker, but does not replan or authorize unrelated C0 descendants.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0

#### Progress note
Included only to satisfy dotted component validation. No whole-task replan is intended.

#### Summary
Validation ancestor for the scoped ExtCall nonstatic success proof repair. No sibling/cousin work is changed by this update.

#### Argument
The only active argument in this update is inside C0.5.4.5.1.2: finish the nonstatic ExtCall success Resume by a branch-local proof that avoids the failed optional-driver premise packaging.

#### Definition design
No semantic definition changes are authorized. All proof-interface changes remain inside `semantics/prop`.

#### Code structure
Do not edit files outside `semantics/prop`.

### C0.1: Baseline audit of reachable residual cheats and authorized edit scope
- Kind: `proof_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Risk 1: mechanical grep/build audit to establish current source obligations and prevent accidental work outside scope.
- Checkpoint: yes
- Carries progress/evidence from: TO_type_system_rewrite-20260601T220715Z_m4389_t002, TO_type_system_rewrite-20260601T220715Z_m4347_t003

#### Progress note
Carries forward prior baseline evidence only as a starting point; rerun because this replacement C0 now authorizes proof work and final completion depends on the current source state.

#### Summary
- Confirm the currently reachable cheats in fresh-stack `semantics/prop` sources before editing.
- Expected obligations are `raw_call_return_type_well_formed`, `eval_all_type_sound_mutual[Expr_Call_ExtCall]` sub-suspends/cheats, and `eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
- Verify no source edits are needed outside `semantics/prop`.
- Build `vyperTypeStmtSoundnessTheory` and/or `vyperSemanticsHolTheory` only as baseline evidence, not as completion while cheats remain.

#### Statement
Audit obligation: source grep plus focused build establishes the exact current remaining reachable cheats under `semantics/prop` before proof edits begin.

#### Approach
Use grep for `cheat`, `CHEAT`, and the named theorem/Resume labels in `semantics/prop/*.sml`, then run a focused holbuild target if permitted by the component gate. Record any discrepancy in `STATE_type_system_rewrite.md` and stop if the residual obligations differ materially from this PLAN.

#### Not to try
Do not treat baseline build success as proof completion. Do not stage pre-existing unrelated untracked files such as legacy learning/temp artifacts.

### C0.2: Remove localized raw_call return-type well-formedness cheat
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: Risk 1: the current proof is a localized arithmetic proof around `word_size`; it already has supporting lemmas `word_size_le` and `word_size_not_lt_self` immediately above the theorem.
- Dependencies: C0.1

#### Progress note
New proof-completion leaf for the reachable builtins cheat listed in the task plan audit.

#### Summary
- Prove `raw_call_return_type_well_formed` in `vyperTypeBuiltinsScript.sml` without `cheat`.
- Use `Cases_on flags` and unfold `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`.
- The only nontrivial branch is the max-outsize/word-size arithmetic; use existing `word_size_le` and `word_size_not_lt_self`.
- Build `vyperTypeBuiltinsTheory` or the next dependent focused target afterwards.

#### Statement
```sml
Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
```

#### Approach
Keep the proof local: destruct `flags`, rewrite the return-type definition, then discharge slot-size side conditions by deriving `word_size n ≤ n`; case split on `word_size n < n`, and in the equality corner use `word_size_not_lt_self`. Avoid introducing a new arithmetic abstraction unless HOL cannot close the final numeric subgoal with `decide_tac`/existing arithmetic simps.

#### Not to try
Do not change `raw_call_return_type_def` or weaken the theorem. Do not move this into statement soundness; it is an independent builtins lemma and should be closed before larger integration work.

### C0.3: ExtCall compact branch-boundary probe from projected helper interface
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Risk 2: it is a small authorized probe using already-proved local projected helper lemmas; it deliberately checks that the new interface avoids the old generated-prefix fanout before full ExtCall integration.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: E0223
- Progress transition: `replacement`
- Carries progress/evidence from: E0223, TO_type_system_rewrite-20260601T220715Z_m4328_t001

#### Progress note
Uses E0223 as negative evidence: the probe is successful only if it reaches/apply a compact projected helper without exposing the 9-goal generated-prefix failure shape.

#### Summary
- In `vyperTypeStmtSoundnessScript.sml`, test the replacement ExtCall proof boundary before removing the main cheat.
- Target the branch after argument evaluation succeeds, using existing `extcall_static_projected_sound` and/or `extcall_nonstatic_projected_state_well_typed` style lemmas.
- The probe should demonstrate one compact call to a projected helper from assumptions `eval_exprs ... = (INL vs,args_st)`, runtime-typed args, well-formed return type, and conditional driver IH.
- Stop/escalate if HOL again exposes generated-prefix fanout or a multi-KiB optional-driver premise before helper application.

#### Statement
Probe output: a small local theorem or temporary proof skeleton showing that a concrete ExtCall success branch can be closed by a projected helper without generated-prefix reconstruction. If kept, it should have a stable theorem name such as `extcall_static_projected_sound_from_resume_assumptions[local]`; if not needed, record the successful proof shape in the main proof edit.

#### Approach
Do not begin at the old `Expr_Call_ExtCall_result_static_success` fanout. Instead, factor the needed assumptions out of the Resume context: after `eval_exprs` succeeds and the `well_typed_expr` ExtCall case has yielded `MAP expr_type`/`well_typed_opt`/return-type facts, call the projected lemma. If the generated mutual IH for `drv` is too broad, pass it only under the projected lemma's conditional driver premise and only in the branch where `returnData = [] ∧ IS_SOME drv`.

#### Not to try
Do not run `AllCaseEqs()` over the whole evaluator prefix. Do not prove generated-prefix adapter theorems. Do not attempt to solve the old 9 generated-prefix goals individually; that is a failed boundary, not a proof obligation.

### C0.4: Static ExtCall proof-boundary repair using generated-IH passthrough then concrete tail
- Kind: `proof_boundary_refactor`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Risk 2: E0241 shows the previous branch-local tail proof exposed a generated optional-driver premise before the concrete tail. That premise is an administrative mutual-induction artifact already present in the Resume context, so close it by direct assumption matching; the remaining tail uses existing local ExtCall lemmas.
- Supersedes: C0.4@previous, C0.4.3@previous, E0241
- Progress transition: `replacement`
- Carries progress/evidence from: C0.4.1, C0.4.2, E0239, E0240
- Invalidates prior progress/evidence: C0.4.3@previous

#### Progress note
Carry forward the prefix/error work. Invalidate only the previous C0.4.3 assumption that the `SOME result` tail is immediately branch-local after `Cases_on run_ext_call`.

#### Summary
Keep the static ExtCall prefix/error subresumes that already build. After `run_ext_call` is split, first close the generated optional-driver premise by direct `MATCH_ACCEPT_TAC`/targeted assumption matching, without stripping or simplifying its prefix. Only then enter the concrete `SOME (success,returnData,accounts',tStorage')` tail. The concrete tail should use existing local boundary lemmas, not broad generated-prefix cleanup.

#### Argument
The static ExtCall proof has two distinct obligations after reaching `run_ext_call`: pass through the generated optional-driver premise required by the mutual induction package, then prove the concrete semantic tail. E0241 shows these were conflated. The generated premise goal has the same long shape as the generated IH assumption already present in the Resume context (the one existing error subresumes discard with `kall_tac`), so it should be accepted opaquely before any tail simplification. Once removed, the `NONE`, revert, non-empty-return/decode, and driver-continuation cases are ordinary monadic tail cases. State/account facts come from `run_ext_call_accounts_well_typed` and tail soundness lemmas; the driver-continuation case specializes the generated premise only once the concrete branch supplies `returnData = []` and `IS_SOME drv`.

#### Definition design
No definitions change. Treat the generated optional-driver premise as an opaque proof-interface artifact. Probe success means the large generated premise goal closes from an existing assumption of the same shape without `gvs[]`, `AllCaseEqs()`, stripping, manual prefix-variable instantiation, or a generated-prefix adapter theorem. Concrete-tail consumers should use `run_ext_call_accounts_well_typed`, `extcall_after_state_update_tail_sound`, and related local ExtCall lemmas instead of unfolding the earlier prefix.

#### Code structure
Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`. In `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`, replace the final `cheat` with a structured proof: split `run_ext_call`, immediately discharge the generated-IH passthrough goal, delegate/keep the `NONE` subresume, then handle the concrete `SOME` tail linearly. If a tiny helper is needed, place it near the existing local `extcall_*` helper block; do not add a long theorem restating the generated prefix.

### C0.4.1: Audit continuation-helper interface and current static-success prefix
- Kind: `proof_boundary_probe`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed by E0239; retained as carried-forward evidence.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.4.1, E0239

#### Progress note
Still valid because it does not depend on the invalidated tail-locality assumption.

#### Summary
Carried-forward audit of the static ExtCall helper interface and prefix state. No executor work remains.

### C0.4.2: Close static ExtCall prefix error subresumes
- Kind: `mutual_resume_proof`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: Already completed by E0240; the calldata and empty-code error branches remain isolated and valid.
- Dependencies: C0.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.4.2, E0240

#### Progress note
Unaffected by the `run_ext_call` boundary repair.

#### Summary
Carried-forward static ExtCall prefix error branch proofs. No new work remains.

### C0.4.3: Close static ExtCall run/tail after generated-IH passthrough
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: Replaces the prior stuck leaf. With the generated-IH passthrough split out, remaining leaves are small and use existing subresumes/lemmas.
- Dependencies: C0.4.2
- Supersedes: C0.4.3@previous, E0241
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C0.4.3@previous

#### Progress note
E0241 is accepted as valid risk-mismatch evidence and invalidates the old branch-local tail plan.

#### Summary
First close the administrative generated optional-driver premise opaquely. Keep the existing `run_ext_call = NONE` subresume/proof as the failure branch. Then prove the concrete `SOME` tail by tuple/case splitting on `success` and `returnData`, using local tail lemmas rather than generated-prefix simplification.

#### Approach
At the current cheat in `Expr_Call_ExtCall_result_static_success`, do not try to rename the `SOME` branch first. After `Cases_on run_ext_call ...`, close the leading generated-premise goal by direct assumption matching, then continue to option branches. Drive the concrete tail from the saved `(do _ od) args_st = (res,st')` equality.

#### Not to try
Do not use broad `gvs[]`, `AllCaseEqs()`, long generated-prefix adapter theorems, or `rpt strip_tac >> first_x_assum drule_all` on the generated premise; E0241 shows that path is brittle and forbidden.

### C0.4.3.a: Discharge the generated optional-driver premise by direct IH passthrough
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 0
- Work units: 1
- Rationale: The exact assumption shape is long, but E0241 exposes the goal and existing error subresumes confirm the same generated assumption is in context. This is targeted assumption acceptance, not a semantic proof.
- Checkpoint: yes
- Supersedes: E0241

#### Summary
After the `run_ext_call` split, close the large generated optional-driver premise by matching an existing context assumption of the same `!s'' vs ... . _` shape. This checkpoint succeeds only if it closes without `gvs[]`, prefix case cleanup, stripping, or manual instantiation.

#### Statement
In `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`, close the generated premise goal of shape `!s'' vs t ... . <ExtCall prefix conjuncts> /\ returnData = [] /\ IS_SOME drv ==> !env st res st'. ... eval_expr cx (THE drv) st = (res,st') ==> ...` directly from the existing generated-IH assumption.

#### Approach
Use targeted `qpat_x_assum` with a pattern on the final consequent involving `eval_expr cx (THE drv)` and then `MATCH_ACCEPT_TAC`/equivalent to accept the assumption wholesale. If selection is noisy, move or discard unrelated assumptions, but do not strip the generated premise. Build with a deliberate suspend after this passthrough to confirm the concrete tail is next.

#### Not to try
Do not `rpt strip_tac`; do not use `first_x_assum drule_all`; do not simplify the generated prefix.

### C0.4.3.b: Carry forward/verify the `run_ext_call = NONE` static branch
- Kind: `mutual_resume_proof`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: The `Expr_Call_ExtCall_static_run_none` subresume is already present and builds; it is a monadic runtime-error branch.
- Dependencies: C0.4.3.a
- Progress transition: `carry_forward`
- Carries progress/evidence from: Expr_Call_ExtCall_static_run_none, TO_type_system_rewrite-20260602T125148Z_m4555_t001

#### Progress note
Verify it is still referenced correctly after the repaired split; otherwise carry forward the existing proof.

#### Summary
Keep/verify the existing static `run_ext_call = NONE` subresume. It rewrites known prefix facts and yields a runtime error, so no new semantic argument is needed.

#### Approach
Only edit the suspend/reference name if the parent wrapper changes. The proof should remain a local monadic rewrite ending with `no_type_error_result_def`.

#### Not to try
Do not re-prove this branch in the parent by destructing the whole generated prefix.

### C0.4.3.c: Close the concrete `SOME` ExtCall tail
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: After C0.4.3.a removes the administrative premise, the tail follows the existing local proof pattern: destruct tuple/success, close error cases, use `run_ext_call_accounts_well_typed` and `extcall_after_state_update_tail_sound` for success.
- Dependencies: C0.4.3.a, C0.4.3.b
- Checkpoint: yes
- Supersedes: C0.4.3@previous
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C0.4.3@previous

#### Progress note
Repaired executable replacement for the old C0.4.3 success-tail proof.

#### Summary
Prove the `run_ext_call = SOME result` tail after generated-IH passthrough. Rewrite only the saved monadic equality and known prefix facts, destruct `result` into `(success,returnData,accounts',tStorage')`, close `success = F` as runtime error, and prove `success = T` with existing account/state/tail lemmas. Specialize the generated driver premise only in the concrete `returnData = [] /\ IS_SOME drv` subcase.

#### Statement
Complete `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` for the branch `run_ext_call cx.txn.target target_addr x' NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn) = SOME result`.

#### Approach
Follow the static projected proof pattern already in the file: move the saved `(do _ od) args_st = (res,st')` equality, rewrite only local monad/state defs plus the concrete run result, then destruct the result tuple and `success`. For `success = T`, derive `accounts_well_typed accounts'`, establish `runtime_consistent env cx args_st`, rewrite `get_tenv cx = env.type_defs`, and invoke `extcall_after_state_update_tail_sound`.

#### Not to try
Do not simplify the entire post-run state. Do not create a long prefix adapter theorem. Do not instantiate the generated premise before the concrete success branch supplies `returnData = []` and `IS_SOME drv`.

### C0.4.4: Collapse outer static wrapper and remove obsolete static-success scaffolding
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: Once C0.4.3 closes, cleanup is mechanical and build/audit based.
- Dependencies: C0.4.3.c
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.4@previous

#### Progress note
Same cleanup obligation, refined for the generated-IH passthrough step.

#### Summary
After static success closes, remove obsolete failed-tail scaffolding, keep helpers/subresumes still used, ensure the parent Resume has no cheat, and build `vyperTypeStmtSoundnessTheory`.

#### Approach
Audit only the static ExtCall area of `vyperTypeStmtSoundnessScript.sml`. Do not touch nonstatic ExtCall or files outside `semantics/prop`.

#### Not to try
Do not perform broad repository cleanup or edit unrelated cheats.

### C0.5: ExtCall/call soundness context
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Validation parent only; risk follows the replacement of the descendant blocker by executable low-risk children. No sibling work under C0.5 is replanned here.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5

#### Progress note
Carry-forward context for scoped replacement only.

#### Summary
Ancestor context for the ExtCall proof subtree. The only modified obligation is C0.5.4.5.1.2.

#### Argument
ExtCall soundness should be proved branch-locally: close error and non-driver branches immediately, and consume recursive IHs only at concrete recursive calls.

#### Definition design
Use existing local proof interfaces; do not change evaluator definitions.

#### Code structure
Keep edits in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and task/state files under `semantics/prop`.

### C0.5.1: Baseline audit: keep the failed full-call nonstatic helper out of the source
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: E0249 reports the failed helper was removed and the focused build is clean. This leaf is a mechanical audit/commit boundary before adding new branch-local helpers.
- Supersedes: C0.5.1@E0249
- Progress transition: `replacement`
- Carries progress/evidence from: E0249, TO_type_system_rewrite-20260602T195240Z_m4672_t001
- Invalidates prior progress/evidence: C0.5.1@previous-full-projected-helper-strategy

#### Progress note
The E0249 closure evidence validly establishes the source was reverted and builds clean; this component converts that into an explicit baseline audit.

#### Summary
- Confirm `extcall_nonstatic_projected_sound` is not present unless it is already fully proved by a later deliberate replan.
- Confirm `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` still contains only the intentional cheat before this subtree begins.
- Run the focused build to ensure the source is stable.
- Do not stage unrelated untracked artifacts.

#### Description
This is a guard against repeating E0249. The repository should be in the reverted clean state before any new proof work is attempted.

#### Statement
Audit/check only: grep for the failed helper name and build `vyperTypeStmtSoundnessTheory` with the intentional nonstatic Resume cheat still present.

#### Approach
Use grep rather than editing unless stale failed scaffolding remains. If any partial `extcall_nonstatic_projected_sound` proof is present, delete it or revert it before proceeding. Build once to verify the baseline.

#### Not to try
Do not attempt to repair the failed full-call helper in place; that is the invalidated strategy.

### C0.5.2: Prove direct nonstatic ExtCall error-branch micro-helpers
- Kind: `boundary_lemma_suite`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: These helpers are small because they must avoid the full generated prefix and only reason from concrete branch outcomes or direct monadic tail equations. Each branch should close by rewriting `return_def`, `raise_def`, `assert_def`, and preservation of unchanged state, not by splitting the whole call.
- Dependencies: C0.5.1
- Carries progress/evidence from: E0249

#### Progress note
New replacement work created from the E0249 diagnosis: branch error closures must be local facts, not generated-prefix cleanup.

#### Summary
- Add local helpers only for already-isolated nonstatic error branches.
- Cover calldata-build failure, target-has-no-code assertion failure, `run_ext_call = NONE`, and `run_ext_call = SOME (F, returnData, accounts', tStorage')` revert/assertion failure if those branches are not closed directly in the Resume.
- Hypotheses should be direct branch facts plus current `state_well_typed`, `env_consistent`, and `accounts_well_typed` facts.
- Conclusions should match the mutual postcondition for the nonstatic ExtCall result so the Resume can use `irule`/`drule`, not manual theorem plumbing.

#### Statement
Suggested shape, split into separate local theorems as needed:

```sml
Theorem extcall_nonstatic_runtime_error_sound[local]:
  state_well_typed cur_st /\ env_consistent env cx cur_st /\
  accounts_well_typed cur_st.accounts /\
  res = INR (Error err) /\ st' = cur_st /\ (* err is a RuntimeError branch, not TypeError *) T ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of INL tv => expr_result_typed env (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) tv | INR _ => T
```

Branch-specific statements are preferable if HOL pattern matching is simpler.

#### Approach
Prefer separate tiny theorems whose conclusions are the exact conjunction required by the mutual postcondition. For runtime error branches, expand `no_type_error_result_def` and avoid any value-typing proof because the result is `INR`. If a branch has unchanged `args_st`, use assumptions about `args_st` directly; if it has just updated accounts/transient storage, leave it to C0.5.3 rather than mixing success-tail logic here.

#### Not to try
Do not state a helper with `eval_expr cx (Call ret_type (ExtCall F ...)) st = (res,st')` as a premise. Do not prove a single mega-helper that case-splits `build_ext_calldata`, no-code, and `run_ext_call`; that is the E0249 timeout shape.

### C0.5.3: Prove/prepare the nonstatic success-tail adapter using the conditional driver IH
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The hard tail proof already exists as `extcall_success_continuation_sound_cond_driver_ih`; this component only aligns the nonstatic success branch with that lemma and the run-call account typing fact. It remains low risk if the statement starts after `run_ext_call = SOME (T, returnData, accounts', tStorage')`.
- Dependencies: C0.5.1
- Checkpoint: yes
- Carries progress/evidence from: C0.4.3.c, E0246

#### Progress note
Carries forward the successful static-tail insight: the conditional driver IH is the correct boundary, but now applied only after the nonstatic success branch is concrete.

#### Summary
- Provide a small adapter for the concrete nonstatic success branch after `run_ext_call` returns `SOME (T, returnData, accounts', tStorage')`.
- Use `run_ext_call_accounts_well_typed` to establish `accounts_well_typed accounts'`.
- Use `runtime_consistent env cx args_st` from the current state/context assumptions.
- Apply `extcall_success_continuation_sound_cond_driver_ih` so the optional-driver IH is required only under `returnData = [] /\ IS_SOME drv`.
- This is a checkpoint because if the conditional-driver IH does not align here, the final Resume strategy must be reconsidered.

#### Statement
Suggested local theorem or direct proof pattern:

```sml
Theorem extcall_nonstatic_success_tail_sound[local]:
  runtime_consistent env cx args_st /\ functions_well_typed cx /\
  accounts_well_typed accounts' /\ well_typed_opt env drv /\
  well_formed_type env.type_defs ret_type /\
  (!e. drv = SOME e ==> expr_type e = ret_type) /\
  (returnData = [] /\ IS_SOME drv ==> driver_ih_for_THE_drv) /\
  (do _ <- assert T (Error (RuntimeError "ExtCall reverted"));
      _ <- update_accounts (K accounts');
      _ <- update_transient (K tStorage');
      if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
      else do ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val)
           od
   od) args_st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of INL tv => expr_result_typed env (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) tv | INR _ => T
```

If this is just an immediate specialization of `extcall_success_continuation_sound_cond_driver_ih`, the executor may skip storing a new theorem and document that the existing lemma is the adapter.

#### Approach
Start after the `run_ext_call` success tuple has been destructed. Establish `accounts_well_typed accounts'` with `drule_all run_ext_call_accounts_well_typed` in the final Resume or as an explicit premise of the adapter. Then apply `extcall_success_continuation_sound_cond_driver_ih` with `is_static = F`; pass the generated optional-driver IH only under the lemma's conditional premise.

#### Not to try
Do not use the older unconditional `extcall_after_state_update_tail_sound` unless the driver IH is already easy to provide; the conditional lemma was introduced to avoid premature specialization. Do not instantiate the generated IH at the top of the Resume before reaching the concrete success-tail branch.

### C0.5.4: Expression call soundness context
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Validation parent only. The previous high risk was due to the descendant C0.5.4.5.1.2 blocker, now replaced by a scoped low-risk branch proof plan.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5.4

#### Progress note
Carry-forward context for scoped replacement only.

#### Summary
Ancestor context for expression-call soundness; only the nonstatic ExtCall success Resume leaf is changed.

#### Argument
The mutual evaluator IH must be consumed at actual recursive evaluator calls, not reconstructed by replaying generated prefixes from the top-level context.

#### Definition design
No definition changes. Desired interface is a branch-local generated IH use.

#### Code structure
No code movement is authorized by this scoped update.

### C0.5.4.5: ExtCall branch soundness context
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Validation parent only. The local descendant now has an executable low-risk proof path splitting the success continuation before IH use.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5.4.5

#### Progress note
Carry-forward context for scoped replacement only.

#### Summary
Ancestor context for ExtCall branches; this update only repairs the nonstatic success Resume proof interface.

#### Argument
For successful ExtCall, after `run_ext_call` returns, soundness reduces to the continuation. The continuation either decodes return data or evaluates the optional driver expression.

#### Definition design
Use existing tail theorem for branches where the driver condition is false; use generated IH directly where the driver condition is true.

#### Code structure
Keep existing local tail theorems; edit only the final Resume suffix for this leaf.

### C0.5.4.5.1: Nonstatic ExtCall success context
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Validation parent only. The scoped child replacement gives a concrete low-risk strategy for the missing optional-driver proof interface.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5.4.5.1

#### Progress note
Carry-forward context for scoped replacement only.

#### Summary
Ancestor context for nonstatic ExtCall success. Stable prefix facts and tail lemmas are preserved; the final Resume suffix is refactored into false-driver and true-driver branches.

#### Argument
The proof is linear through argument evaluation, calldata construction, nonempty code, successful `run_ext_call`, account well-typedness, and final continuation. The only recursive proof obligation is the optional driver expression when `pr1 = []` and `drv` exists.

#### Definition design
No new definitions. The proof interface must stay branch-local and must not introduce a generated-prefix bridge theorem.

#### Code structure
All substantive edits stay in the `Expr_Call_ExtCall_nonstatic_success` Resume in `vyperTypeStmtSoundnessScript.sml`.

### C0.5.4.5.1.1: Carry-forward evidence: tail theorem and prefix facts are valid but insufficient
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0318/E0321 confirmed the local tail theorem and edit point; E0319/E0322 confirmed the two concrete prefix facts build before the final cheat. This is an audit/carry-forward node only, not a proof-producing frontier.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0318, E0319, E0321, E0322, TO_type_system_rewrite-20260602T195240Z_m5838_t001, TO_type_system_rewrite-20260602T195240Z_m5846_t001, TO_type_system_rewrite-20260602T195240Z_m5866_t001

#### Progress note
The carry-forward facts remain true and should be cited in any maintainer report or future redesign, but they do not by themselves close the branch.

#### Summary
- `extcall_nonstatic_success_tail_sound_cond_driver_ih` is present and proved locally.
- The forbidden outside bridge theorem is absent.
- The Resume reaches the planned partial point.
- The value-extraction do-block fact is proved by `EVAL_TAC`.
- The calldata case fact is proved from `build_ext_calldata ... = SOME x'` and `return_def`.
- Focused holbuild succeeds through the intentional final `cheat`.

#### Statement
Audit facts currently in source before the final cheat:

```sml
(do assert T (Error (RuntimeError "ExtCall no value"));
    v <- return amount;
    return (SOME v, TL (TL x)) od) args_st =
  (INL (SOME amount, TL (TL x)), args_st)
```

and

```sml
(case build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL x)) of
   NONE => raise (Error (RuntimeError "ExtCall build_calldata"))
 | SOME v => return v) args_st = (INL x', args_st)
```

#### Approach
No executor action is required for this carry-forward component. Do not rebuild merely for this audit unless a future plan requests it; the cited focused builds already establish the stable partial state.

#### Not to try
Do not reinterpret these prefix facts as proving the optional-driver premise. They are only antecedents for the generated IH; E0320/E0323 show that having them in context is not enough for straightforward IH consumption.

### C0.5.4.5.1.2: Linear nonstatic ExtCall success Resume proof without prefix adapters
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk is lowered from the blocked status because the plan no longer asks the executor to recover a compact optional-driver premise by broad simplification or a generated-prefix adapter. The proof is decomposed into an explicit false-driver/decode branch that can use the existing tail theorem with a vacuous IH premise, and a true-driver branch that consumes the generated optional-driver IH only after the concrete success continuation is isolated. This is exactly the route allowed by the maintainer clarification. If the true-driver branch still exposes a large existential/conditional package or requires selector/indexing search, stop and escalate.
- Supersedes: C0.5.4.5.1.2
- Progress transition: `replacement`
- Carries progress/evidence from: C0.5.4.5.1.2, E0322, E0323, E0324, TO_type_system_rewrite-20260602T195240Z_m5907_t001

#### Progress note
Replaces the previous terminal blocked-status leaf with an executable proof-interface repair inside the same subtree. E0322 stable prefix/tail facts still count. E0323/E0324 remain negative guidance: do not select the generated IH from the unsplit top-level context and do not apply the tail theorem before avoiding or localizing its driver premise.

#### Summary
- Finish only the remaining `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]`.
- Stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and supporting task/STATE files under `semantics/prop`.
- Preserve existing prefix facts, split the final success continuation on `pr1 = [] /\ IS_SOME drv`, and keep one active branch at a time.
- In the non-driver/decode branch, use `extcall_nonstatic_success_tail_sound_cond_driver_ih` with its conditional driver premise discharged by contradiction.
- In the true driver branch, consume the generated optional-driver IH directly at the concrete branch point; do not package it into a separate adapter theorem.

#### Description
This subtree owns the remaining ExtCall nonstatic success Resume obligation. The previous plan tried to apply `extcall_nonstatic_success_tail_sound_cond_driver_ih` uniformly and then simplify its conditional driver premise; that exposed a large existential/conditional package and timed out. The repair is to avoid manufacturing the package in the false/decode branch and to use the generated IH only in the one concrete true-driver branch where the evaluator actually calls `eval_expr cx (THE drv)`.

#### Statement
Source obligation:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]:
  ...
QED
```
with the final `cheat` removed, proving the `Expr_Call_ExtCall_nonstatic_success` case of `eval_all_type_sound_mutual` for nonstatic external calls.

#### Approach
Keep the existing prefix proof through the facts already visible in E0324: evaluated arguments, `build_ext_calldata`, nonempty target code, successful `run_ext_call`, accounts well-typed after the call, `runtime_consistent env cx args_st`, and the final continuation equation. Then case-split the continuation condition `pr1 = [] /\ IS_SOME drv`. The false branch is a tail-theorem application with a vacuous driver premise; the true branch bypasses the tail theorem and applies the generated expression IH directly to the concrete driver evaluation state.

#### Not to try
Do not retry `simp[]` after `irule extcall_nonstatic_success_tail_sound_cond_driver_ih` in the unsplit goal; E0324 showed it leaves the large missing driver-premise package and times out. Do not use broad `simp`/`gvs`/`AllCaseEqs()` over the whole ExtCall prefix, `res_tac`/`imp_res_tac`/large `metis_tac`, numeric `ASSUM_LIST` indexing, or an outside bridge theorem replaying the generated prefix. Do not edit evaluator/semantics definitions or files outside `semantics/prop`.

#### Argument
At the success point of a nonstatic ExtCall, the evaluator has already evaluated arguments, extracted the target address and amount, built calldata, checked target code, and obtained a successful `run_ext_call` result `(T, pr1, pr2, pr3)`. The only remaining computation is the post-call continuation on `args_st with <|accounts := pr2; tStorage := pr3|>`. If `pr1 <> []` or `drv = NONE`, the continuation decodes ABI return data; the already proved tail theorem proves soundness without needing any recursive expression IH because its driver-premise antecedent is false. If `pr1 = []` and `drv = SOME e`, the continuation is exactly `eval_expr cx e` at the updated state; the generated mutual-induction IH for the optional driver is semantically the right proof obligation and should be specialized only in this branch, using the concrete prefix equalities already present. The conclusion of that IH gives soundness for the driver expression, and `well_typed_opt env drv` plus annotation facts identify `expr_type (THE drv) = ret_type`, allowing the result to be rewrapped as `expr_result_typed env (Call ret_type (ExtCall F (...)) es drv)`.

#### Definition design
No semantic definitions are to change. The proof interface is branch-local: existing local theorems `extcall_nonstatic_success_tail_sound_cond_driver_ih`, `runtime_consistent_get_tenv`, `update_accounts_transient_runtime_consistent`, and stable prefix facts are consumers for the non-driver branch; the generated mutual IH is the consumer for the true-driver branch. Failure sign: if a goal contains the full generated existential/conditional prefix package after the branch split, the proof has slipped back into the old interface and must stop rather than add another adapter theorem.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml` unless updating `semantics/prop/STATE_type_system_rewrite.md` or task plan/state files as progress notes. Keep existing local tail theorems around lines 9670-9820; they remain useful. Replace only the final cheated suffix of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]` around lines 18086-18110 with the linear branch proof. Do not introduce a new external bridge theorem for the generated IH; any IH specialization should live inside this Resume branch where generated assumptions are in scope.

### C0.5.4.5.1.2.1: Split the final continuation and close the non-driver/decode branch
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: This is a bounded refactor of the existing Resume suffix. The false branch deliberately avoids the missing driver-premise problem: `pr1 = [] /\ IS_SOME drv` is false, so the conditional IH premise of the existing tail theorem is vacuous.
- Carries progress/evidence from: E0322, E0324

#### Progress note
Uses E0322 stable prefix facts and E0324's observation that the tail theorem matches the desired postcondition except for the driver premise. This child applies the tail theorem only where that premise is immediately false.

#### Summary
- Edit only the final suffix of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]`.
- Preserve existing prefix facts through the successful `run_ext_call` and final continuation equation.
- Case-split on `pr1 = [] /\ IS_SOME drv` before applying any tail theorem.
- In the false branch, apply `extcall_nonstatic_success_tail_sound_cond_driver_ih`; discharge its conditional driver premise by contradiction from the branch condition.
- Leave the true branch for C0.5.4.5.1.2.2; do not try to solve it by simplifying the tail theorem premise.

#### Description
Restructure the currently cheated suffix so the final continuation condition is explicit. This produces one branch where the return-data/driver condition is false and the old tail theorem is safe to use, and one branch where the evaluator definitely calls the optional driver and the generated IH must be consumed directly.

#### Statement
Within the Resume proof, establish the false-condition branch:
```hol
~(pr1 = [] /\ IS_SOME drv) ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env
      (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) tv
  | INR _ => T
```
using the existing success-prefix facts and final continuation equation.

#### Approach
After the current prefix, introduce `Cases_on `pr1 = [] /\ IS_SOME drv`` or an equivalent local split. In the false branch, `irule extcall_nonstatic_success_tail_sound_cond_driver_ih`; solve ordinary premises from existing facts (`runtime_consistent env cx args_st`, `functions_well_typed cx`, `accounts_well_typed pr2`, `well_typed_opt env drv`, `well_formed_type env.type_defs ret_type`, annotation fact, and the continuation equation). For the theorem's conditional driver premise, start with the antecedent `pr1 = [] /\ IS_SOME drv` and close by contradiction with the false branch assumption; do not simplify the entire generated context.

#### Not to try
Do not apply the tail theorem before the case split. Do not run `simp[]` hoping to solve the conditional driver premise in the unsplit context. Do not destruct all monadic prefix operations again; use the existing named prefix equalities already produced before the cheat.

### C0.5.4.5.1.2.2: Close the true driver branch by direct generated-IH consumption
- Kind: `proof`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: The true branch is the only point where the generated optional-driver IH is needed and the maintainer explicitly permits specialization there. The context is concrete: `pr1 = []`, `IS_SOME drv`, the final continuation is `eval_expr cx (THE drv)` at the updated post-call state, and the relevant prefix facts are already split. This avoids the old proof-interface failure of manufacturing a compact premise in the top-level Resume context.
- Dependencies: C0.5.4.5.1.2.1
- Checkpoint: yes
- Carries progress/evidence from: E0322, E0323, E0324

#### Progress note
Carries forward E0322 prefix facts. E0323 is negative evidence to avoid selector/indexing search; here the IH is consumed only after branch-local concretization. E0324 is negative evidence to avoid uniform tail-theorem application in this branch.

#### Summary
- Work only in the true branch `pr1 = [] /\ IS_SOME drv`.
- Destructure `drv` to expose `THE drv` as the concrete driver expression.
- Use `well_typed_opt env drv` and `!e. drv = SOME e ==> expr_type e = ret_type` to obtain driver well-typing and result type.
- Specialize the generated optional-driver IH once, with concrete prefix equalities and the final `eval_expr cx (THE drv)` equation already in scope.
- Use the IH conclusion to prove state/env/accounts/no-type-error and rewrap successful driver values as `expr_result_typed` for the enclosing ExtCall expression.
- Stop if this branch again requires broad generated-prefix cleanup or a long outside adapter theorem.

#### Description
This child fills the remaining true-driver branch left by C0.5.4.5.1.2.1. The proof should be short because all evaluator prefix effects have already been committed to concrete facts. The only recursive call is the optional driver expression; the generated IH should be used directly for that recursive call rather than converted into a reusable theorem.

#### Statement
Within the Resume proof, establish the true-condition branch:
```hol
pr1 = [] /\ IS_SOME drv ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env
      (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) tv
  | INR _ => T
```
from the final continuation equation, which simplifies in this branch to:
```hol
eval_expr cx (THE drv) (args_st with <|accounts := pr2; tStorage := pr3|>) = (res,st')
```

#### Approach
In the true branch, `Cases_on drv` should leave the `SOME e` case only; simplify `THE drv` and obtain `well_typed_expr env (THE drv)` from `well_typed_opt env drv` and `expr_type (THE drv) = ret_type` from the annotation premise. Apply the generated IH whose consequent mentions `eval_expr cx (THE drv)` to the concrete updated state `args_st with <|accounts := pr2; tStorage := pr3|>`, using `runtime_consistent env cx args_st` plus `accounts_well_typed pr2` and `update_accounts_transient_runtime_consistent` to discharge `env_consistent`, `state_well_typed`, `context_well_typed`, and account premises. After the IH gives driver expression soundness, split on `res`; for `INL tv`, unfold only `expr_result_typed_def`, `expr_runtime_typed_def`, and `expr_type_def` for the enclosing `Call`, and use `well_typed_expr_not_hashmap_place` if needed to rule out HashMap place obligations.

#### Not to try
Do not use `first_x_assum`, `last_x_assum`, `qpat_x_assum`, or numeric `ASSUM_LIST` as blind search over the full pre-split Resume context. If pattern selection is needed, match the generated IH by its distinctive conclusion containing `eval_expr cx (THE drv)` and `well_typed_expr env' (THE drv)`, after the branch split has simplified the context. Do not create a theorem outside the Resume that replays the generated prefix. Do not use large `metis_tac` or broad `gvs[AllCaseEqs()]`; if exact IH specialization is not locally manageable, close this component as stuck with the branch-local goal.

### C0.5.4.5.1.2.3: Audit ExtCall nonstatic success closure and record checkpoint
- Kind: `integration_audit`
- Risk: 1
- Work priority: 2
- Work units: 1
- Rationale: Once the true driver branch is proved, verification and progress recording are mechanical. The task explicitly requires plan/state updates and commits without GPG signing; this audit ensures the subtree result is clean before downstream work resumes.
- Dependencies: C0.5.4.5.1.2.2
- Checkpoint: yes

#### Progress note
New terminal audit for the replacement subtree.

#### Summary
- Run the task-scoped build check for `vyperTypeStmtSoundnessTheory` after the Resume cheat is removed.
- Grep the edited Resume region to confirm `Expr_Call_ExtCall_nonstatic_success` no longer contains `cheat`.
- Inspect `git diff` and ensure all edits are under `semantics/prop` and relevant to this subtree.
- Update `semantics/prop/STATE_type_system_rewrite.md` / plan notes with completed component status and any remaining cheats outside this subtree.
- Commit the logical checkpoint with `git commit --no-gpg-sign`; never use GPG signing and never stage unrelated files.

#### Description
Closeout step for the scoped proof replacement. It does not authorize proving unrelated ready leaves or cleaning unrelated cheats. It only verifies that the nonstatic ExtCall success Resume obligation has been closed in a maintainable way and records the checkpoint required by the task workflow.

#### Statement
Audit obligation:
```text
holbuild target vyperTypeStmtSoundnessTheory succeeds after removing the
`Expr_Call_ExtCall_nonstatic_success` cheat, with edits confined to semantics/prop.
```

#### Approach
Run `holbuild` on `vyperTypeStmtSoundnessTheory` with the normal timeout after the proof edit. Use grep around `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]` to confirm no local cheat remains. Then inspect status/diff, update the state/progress file under `semantics/prop`, stage only relevant files, and commit with `git commit --no-gpg-sign`.

#### Not to try
Do not commit if holbuild fails, if a cheat remains in this Resume, or if the diff contains unrelated files. Do not use `git add -A` and do not run a signed commit. Do not claim the whole task is complete if other task-scoped cheats remain outside this component.

### C0.5.4.6: Audit the completed nonstatic ExtCall Resume and source stability
- Kind: `proof_audit`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: After C0.5.4.5 closes, this is mechanical verification: the subtree should contain no remaining cheat in the nonstatic ExtCall success Resume, and focused holbuild should pass. It preserves the downstream dependency target expected by C0.5.5.
- Dependencies: C0.5.4.5
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5.4.6

#### Progress note
Same audit obligation as the old C0.5.4.6, retained under the same ID so downstream dependencies remain valid.

#### Summary
- Run focused build after the success Resume proof.
- Confirm the nonstatic ExtCall success Resume no longer contains `cheat`.
- Confirm no forbidden broad prefix adapter or whole-prefix cleanup was introduced.
- Confirm edits are confined to `semantics/prop`.
- Preserve C0.5.4.6 as the downstream dependency target for later work.

#### Statement
Focused build/audit obligation: `semantics/prop/vyperTypeStmtSoundnessScript.sml` builds after the nonstatic ExtCall success Resume is proved, and the local ExtCall success Resume no longer contains `cheat`.

#### Approach
Run the focused HOL build used in previous C0.5.4 checkpoints. Inspect the local region around `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]` and the helper block around `extcall_after_state_update_tail_sound_cond_driver_ih_get_tenv` to ensure there are no temporary assertions, no broad generated-prefix adapter theorem, and no unrelated edits outside `semantics/prop`. Commit the successful proof/audit without GPG signing if the task workflow requires a commit.

#### Not to try
Do not broaden this audit to unrelated repository cheats such as later RawCall/RawLog obligations unless the current task plan explicitly schedules them. Do not clean or refactor unrelated temporary/untracked files outside the ExtCall proof path.

### C0.5.5: Terminal audit nonstatic ExtCall completion and remove only planned cheats
- Kind: `proof_audit`
- Risk: 1
- Work priority: 60
- Work units: 2
- Rationale: E0258 correctly found that this audit was premature. With the dependency repaired to C0.5.4.6, it becomes a mechanical terminal audit again.
- Dependencies: C0.5.4.6
- Checkpoint: yes
- Supersedes: C0.5.5@E0258-premature-schedule
- Progress transition: `refinement`
- Carries progress/evidence from: C0.5.5@previous, E0249, E0258

#### Progress note
E0258 is accepted as evidence that the audit must be delayed until C0.5.4.6. It does not close C0.5.5; it refines its dependency so it cannot run before the success proof and local audit.

#### Summary
- Terminal audit for the whole C0.5 nonstatic ExtCall subtree.
- Must run only after C0.5.4.6, not before C0.5.4.4/C0.5.4.5.
- Verify the nonstatic ExtCall success Resume no longer contains `cheat`.
- Verify no failed `extcall_nonstatic_projected_sound` scaffold remains.
- Run focused `holbuild` and commit only task-scoped, unsigned changes.

#### Statement
Audit/check only: grep the nonstatic Resume, `extcall_nonstatic_projected_sound`, and remaining `cheat` occurrences in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, then build `vyperTypeStmtSoundnessTheory`.

#### Approach
Repeat the E0258 audit only after C0.5.4.6 is complete. A remaining `cheat` in `Expr_Call_ExtCall_nonstatic_success` is then a failure of C0.5.4.5/C0.5.4.6, not something to ignore.

#### Not to try
Do not run this audit early. Do not perform opportunistic cleanup outside `semantics/prop`, and do not treat a clean build with a task-scoped planned cheat as completion.

### C0.6: Close RawCallTarget statement-expression soundness cheat after ExtCall integration
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 70
- Work units: 5
- Rationale: Risk 2: RawCallTarget is a single remaining expression-call branch, but it must not run before nonstatic ExtCall is fully integrated because both are residual call-case soundness Resumes in the same proof region and RawCall should not be debugged while the ExtCall prefix boundary is still unstable. The proof is expected to be branch-local and straightforward using existing `raw_call_return_type_well_formed`; if it exposes a missing compact RawCall helper, stop as NEW_DEPENDENCY rather than continuing with theorem plumbing.
- Dependencies: C0.2, C0.5.5
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.6

#### Progress note
This keeps the same RawCallTarget obligation but repairs the schedule: C0.6 now depends on the concrete nonstatic ExtCall integration leaf `C0.5.5`, not the grouping component `C0.5`. No prior RawCall proof progress is lost because C0.6 had not started.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` and remove the RawCallTarget cheat.
- This component is intentionally scheduled after `C0.5.5`, so the next coherent frontier is the nonstatic ExtCall helper sequence, not RawCall.
- Use the combined mutual postcondition: state/env/accounts preservation, no-TypeError, and result typing together.
- Use `raw_call_return_type_well_formed` from `vyperTypeBuiltinsScript.sml` rather than reproving return-type well-formedness.
- Split raw-call evaluator branches linearly and close error cases immediately; stop if that is not straightforward.

#### Description
C0.6 is a post-ExtCall residual cheat closure. The executor should not begin it while `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` remains intentionally cheated, because any call-case proof-boundary issue discovered in ExtCall should inform RawCall proof style first. Once C0.5.5 is complete and the focused theory builds, RawCallTarget should be approached as a single branch-local Resume proof, not decomposed in advance.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  ...
QED
```

#### Approach
Begin only after C0.5.5 and a clean focused build. Rewrite the relevant `well_typed_expr` call case once to expose typed arguments, flags, and `raw_call_return_type` facts. Step through raw-call evaluation one branch at a time; close deterministic error/no-update branches immediately, and use `raw_call_return_type_well_formed` for the success result-typing side condition. If a reusable theorem is genuinely needed, it should be a local RawCall projected helper whose conclusion is exactly the full mutual postcondition, but do not pre-split C0.6 unless the first honest proof attempt reports NEW_DEPENDENCY.

#### Not to try
Do not begin C0.6 before C0.5.5 is proved. Do not unfold old retired type-soundness theories or use legacy `vyperTypeSoundnessScript` facts unless they are already imported and clearly fresh-stack compatible. Do not solve RawCall by weakening result typing, changing `raw_call_return_type_def`, broad-cleaning the entire evaluator prefix, or building long generated-prefix adapter theorems.

### C0.7: Final fresh-stack proof-integrity build, cheat audit, and task-local status commit
- Kind: `final_audit`
- Risk: 1
- Work priority: 60
- Work units: 2
- Rationale: Risk 1: mechanical build/grep/status verification after all proof leaves are closed.
- Dependencies: C0.6
- Checkpoint: yes

#### Progress note
Final validation leaf for the replacement proof-completion subtree.

#### Summary
- Build the relevant target(s), ending with `vyperSemanticsHolTheory` if feasible under task timing.
- Audit for zero reachable CHEAT warnings and no remaining source `cheat` proofs in fresh-stack imported files.
- Update `TYPE_SYSTEM_REWRITE_PLAN.md` / `STATE_type_system_rewrite.md` with actual completion evidence.
- Commit only task-local changes under `semantics/prop` with `git commit --no-gpg-sign`.

#### Statement
Final audit obligation: `vyperSemanticsHolTheory` builds with no reachable fresh-stack CHEAT warnings and the task-local residual source cheats are gone.

#### Approach
Run focused builds first (`vyperTypeBuiltinsTheory`, `vyperTypeStmtSoundnessTheory`) and then the aggregate target. Use grep/source audit to confirm no `cheat` remains at the planned sites and no CHEAT warning is reachable from `vyperSemanticsHolTheory`. Check `git status` carefully; stage only intended `semantics/prop` tracked files and commit unsigned.

#### Not to try
Do not commit unrelated untracked legacy/temp files. Do not call the session complete if any planned cheat remains, even if the build succeeds.
