# PLAN

## Structured Components

### C0: Type-system rewrite proof obligations
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: This merge only repairs C0.5 scheduling. The remaining C0.5 work is decomposed into Risk 1-2 leaves; no sibling or whole-task strategy is invalidated by E0258.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, C0.4, E0254, E0255, E0256, E0257, E0258

#### Progress note
Carry forward all prior C0 progress; E0258 only corrects premature scheduling of C0.5.5.

#### Summary
- Parent grouping for task-scoped type-system rewrite obligations.
- Current update repairs only the nonstatic ExtCall audit scheduling under C0.5.
- Prior static ExtCall work remains valid.
- The next intended live leaf is C0.5.4.4.

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

### C0.5: Nonstatic ExtCall proof via branch-local micro-helpers and linear Resume integration
- Kind: `proof_boundary_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The remaining risk after E0258 is scheduling/dependency bookkeeping. E0254-E0256 proved the skeleton and error subresumes; E0257 identified the local success-boundary repair; E0258 confirms the terminal audit was prematurely scheduled. With carry-forward and corrected dependencies, the remaining leaves are low-risk proof refactor/proof/audit work.
- Progress transition: `refinement`
- Carries progress/evidence from: E0248, E0249, C0.4, E0254, E0255, E0256, E0257, E0258

#### Progress note
Accepts E0258 as evidence that C0.5.5 was a premature audit, not evidence against the nonstatic ExtCall proof strategy. The already-proved C0.5.4.1-.3 work remains valid and is carried forward explicitly so the next executable leaf is the repaired success-boundary refactor C0.5.4.4.

#### Summary
- Complete the nonstatic ExtCall proof without changing evaluator or semantics definitions.
- Carry forward the proved branch-suspended skeleton and error subresumes from E0254-E0256.
- Repair the success suspend boundary before the success proof: derive a compact optional-driver IH before suspending, rather than recovering it from a generated prefix inside the subresume.
- Prove the success subresume using that compact boundary and existing success-tail helpers.
- Run the terminal audit only after C0.5.4.6, never before the success cheat is removed.

#### Description
This merge repairs the C0.5 scheduling error exposed by E0258. The proof strategy remains branch-local: do not revive a full projected nonstatic ExtCall helper, and do not simplify the generated prefix broadly. The remaining substantive repair is local to the success branch boundary.

#### Argument
The nonstatic ExtCall proof follows the evaluator chain one concrete branch at a time. E0254 created a skeleton with named branch suspends; E0255 and E0256 discharged all non-success subresumes. The success branch needs a compact optional-driver IH at the suspend boundary: derive it while still in the parent skeleton, where the static-proof-style generated-prefix antecedent can be specialized once, then pass it as a small assumption into the success subresume. The success subresume then applies the existing post-update/tail soundness helpers without reopening the whole generated prefix. Final correctness is checked by a separate audit after all subresumes build without the planned nonstatic cheat.

#### Definition design
No evaluator, semantics, or typing definitions may change. The proof interface boundary is the Resume/suspend structure in `vyperTypeStmtSoundnessScript.sml`: branch subresumes should receive concrete equations and compact assumptions, not generated-prefix universal antecedents. Failure sign: any remaining proof attempts to derive the optional-driver premise inside `Expr_Call_ExtCall_nonstatic_success` by broad `simp`/`gvs`, `AllCaseEqs()`, or large generated-prefix adapter theorems.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep the proved skeleton and error subresumes. Modify the parent nonstatic Resume/suspend boundary as needed for C0.5.4.4, then fill the `Expr_Call_ExtCall_nonstatic_success` Resume in C0.5.4.5. The final C0.5.4.6/C0.5.5 audits grep for remaining task-scoped cheats and failed scaffolding and run the focused `holbuild`; commits must be unsigned and task-scoped.

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

### C0.5.4: Complete the nonstatic ExtCall Resume with a strengthened success boundary
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: The parent proof is no longer a monolithic risky Resume. E0254-E0256 prove the skeleton and error branches; the only remaining proof work is the success-boundary refactor and success subresume, followed by audit.
- Dependencies: C0.5.1, C0.5.2, C0.5.3
- Progress transition: `refinement`
- Carries progress/evidence from: E0254, E0255, E0256, E0257

#### Progress note
Keeps the branch-suspended proof structure and completed error branches; refines only the success-boundary schedule after E0257/E0258.

#### Summary
- Parent for the final nonstatic ExtCall Resume work.
- C0.5.4.1-.3 are carried forward from E0254-E0256 and should not be redone.
- C0.5.4.4 is the next executable leaf and repairs the success suspend boundary.
- C0.5.4.5 proves the success subresume after the compact IH is available.
- C0.5.4.6 audits that the completed Resume builds without the planned nonstatic success cheat.

#### Argument
The parent Resume has already been decomposed into named subresumes. The error branches close from concrete branch equations. The success branch is true by the existing tail-soundness infrastructure once the optional-driver IH is made available in compact form at the suspend boundary.

#### Definition design
The key proof interface is the success suspend payload. It must include the concrete success-tail equation, updated accounts/transient-storage facts, and a compact optional-driver IH assumption usable directly by the tail helper. Do not make the subresume reconstruct these facts from the generated-prefix universal.

#### Code structure
Work in the existing nonstatic ExtCall Resume and `Expr_Call_ExtCall_nonstatic_success` Resume blocks. Preserve proved Resume blocks for calldata, no-code, run-none, and revert. The audit leaf checks the local source region and focused build.

### C0.5.4.1: Carry forward the nonstatic ExtCall branch-suspended Resume skeleton
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0254 proved the branch-suspended skeleton and focused build. No additional work is needed unless the C0.5.4.4 boundary refactor edits the success suspend payload.
- Dependencies: C0.5.1, C0.5.2, C0.5.3
- Supersedes: C0.5.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0254

#### Progress note
E0254 already completed this skeleton. Treat this leaf as satisfied/carry-forward; the next live edit is C0.5.4.4.

#### Summary
- Carried forward from E0254.
- The parent nonstatic Resume skeleton exists and builds with named subresumes.
- Do not redo this component as a separate edit.
- Later success-boundary changes belong to C0.5.4.4.

#### Statement
Carry-forward checkpoint only: the branch-suspended nonstatic ExtCall Resume skeleton from E0254 remains the baseline.

#### Approach
No executor proof work should be scheduled here. If source inspection is needed while doing C0.5.4.4, preserve the skeleton and edit only the success suspend boundary.

#### Not to try
Do not restart the full nonstatic Resume proof or reintroduce a monolithic projected helper.

### C0.5.4.2: Carry forward the nonstatic calldata-error subresume proof
- Kind: `mutual_subresume_proof`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: E0255 proved the calldata-error subresume with a focused build and without forbidden generated-prefix simplification.
- Dependencies: C0.5.4.1
- Supersedes: C0.5.4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0255

#### Progress note
E0255 already completed this branch. It remains valid and should not block C0.5.4.4.

#### Summary
- Carried forward from E0255.
- The calldata-error subresume is proved and builds.
- No additional proof work is scheduled.
- It remains a dependency fact for the completed nonstatic Resume audit.

#### Statement
Carry-forward checkpoint only: the `Expr_Call_ExtCall_nonstatic_calldata_error` Resume proof from E0255 remains valid.

#### Approach
Do not edit this branch unless a later build shows it was accidentally broken by the success-boundary refactor.

#### Not to try
Do not reopen the generated prefix or replace the branch-local proof with a larger helper.

### C0.5.4.3: Carry forward the nonstatic empty-code, run-none, and revert-error subresume proofs
- Kind: `mutual_subresume_proof`
- Risk: 1
- Work priority: 20
- Work units: 0
- Rationale: E0256 proved the remaining non-success subresumes with a focused build.
- Dependencies: C0.5.4.2
- Supersedes: C0.5.4.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0256

#### Progress note
E0256 already completed these branches. They remain valid and should not be scheduled before C0.5.4.4.

#### Summary
- Carried forward from E0256.
- Empty-code, run-none, and revert-error subresumes are proved and build.
- No additional proof work is scheduled.
- These branches are unaffected by the success optional-driver boundary repair.

#### Statement
Carry-forward checkpoint only: the nonstatic empty-code, run-none, and revert-error Resume proofs from E0256 remain valid.

#### Approach
Do not edit these branches unless the success-boundary refactor accidentally breaks the build.

#### Not to try
Do not broaden these branch proofs into generated-prefix simplification.

### C0.5.4.4: Strengthen the nonstatic success suspend boundary with a compact driver IH
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: E0257 showed that deriving the optional-driver IH inside the success subresume recreates the forbidden generated-prefix simplification. The low-risk repair is to move that derivation to the parent skeleton/suspend boundary so the success subresume receives a compact assumption.
- Dependencies: C0.5.4.1, C0.5.4.2, C0.5.4.3
- Checkpoint: yes
- Supersedes: C0.5.4.4@E0257
- Progress transition: `refinement`
- Carries progress/evidence from: E0257

#### Progress note
Refines the stuck C0.5.4.4 attempt: do not prove the success subresume yet; first repair the suspend boundary so the needed optional-driver IH is passed in compact form.

#### Summary
- This is the next executable leaf after the E0258 schedule repair.
- Edit the parent nonstatic Resume/suspend boundary, not the success proof body first.
- Derive a compact optional-driver IH before suspending the success branch, following the static proof pattern around the corresponding static success split.
- Pass that compact assumption into `Expr_Call_ExtCall_nonstatic_success` so the subresume need not simplify the generated prefix.
- Build with the success subresume still allowed to remain cheated after the boundary refactor.

#### Statement
Refactor/checkpoint obligation: the success suspend payload for `Expr_Call_ExtCall_nonstatic_success` includes a compact assumption sufficient for the optional-driver case of `extcall_success_continuation_sound_cond_driver_ih` or the after-state-update tail helper.

#### Approach
Work in the parent `Expr_Call_ExtCall_result_nonstatic` Resume where the branch is split into success and revert. Before calling `suspend` for success, specialize the generated optional-driver IH once in the concrete success-continuation context and bind it as a small universally/conditionally shaped assumption over the driver expression. Then change the success Resume context to consume that assumption directly; keep the success proof as `cheat` if necessary for this checkpoint, but the focused build must pass.

#### Not to try
Do not recover the driver premise inside `Expr_Call_ExtCall_nonstatic_success` by broad `simp`/`gvs`, `AllCaseEqs()`, or long generated-prefix adapter theorems. Do not manually instantiate a huge generated-prefix theorem in the success subresume; if the subresume still sees only the large universal antecedent, this component has not achieved its interface goal.

### C0.5.4.5: Prove the nonstatic success subresume using the strengthened boundary
- Kind: `mutual_subresume_proof`
- Risk: 2
- Work priority: 40
- Work units: 3
- Rationale: Once C0.5.4.4 supplies the compact optional-driver IH at the suspend boundary, the success proof should be a direct application of existing account-typing and success-tail soundness helpers.
- Dependencies: C0.5.4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0257

#### Progress note
This keeps the intended success proof but depends on the repaired boundary rather than trying to derive the optional-driver IH locally from the generated prefix.

#### Summary
- Fill `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]`.
- Use the compact optional-driver IH assumption supplied by C0.5.4.4.
- Use `run_ext_call_accounts_well_typed`, runtime consistency facts, and the existing success-tail helper.
- Remove the task-scoped `cheat` for this success subresume.
- Run focused `holbuild`.

#### Statement
Theorem/Resume obligation: `eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]` is proved without `cheat`.

#### Approach
Start with `RESUME_TAC`, discard irrelevant generated-prefix assumptions if a compact IH is already present, establish updated accounts typing and runtime consistency, then apply the success-tail soundness helper. The compact optional-driver IH should be consumed by `drule`/`irule` style reasoning, not by reconstructing the whole call prefix.

#### Not to try
Do not unfold the whole evaluator prefix or replay the static full-call proof. Do not use large `metis_tac` or manual `qspecl_then` plumbing to reconstruct the driver IH; if that is needed, return to C0.5.4.4.

### C0.5.4.6: Audit the completed nonstatic ExtCall Resume and source stability
- Kind: `proof_audit`
- Risk: 1
- Work priority: 50
- Work units: 1
- Rationale: After the success subresume is proved, this is a mechanical local audit before the terminal C0.5 audit.
- Dependencies: C0.5.4.5
- Progress transition: `refinement`
- Carries progress/evidence from: E0258

#### Progress note
Added/retained as the local audit that must precede C0.5.5; this prevents the premature terminal audit seen in E0258.

#### Summary
- Grep the nonstatic ExtCall Resume region for remaining planned success cheats.
- Confirm failed full-call projected helper scaffolding is absent.
- Run focused `holbuild` for `vyperTypeStmtSoundnessTheory`.
- Do not commit unrelated files.

#### Statement
Audit/check only for the completed C0.5.4 Resume.

#### Approach
Inspect the exact nonstatic ExtCall Resume and helper regions. The focused build must succeed after the success `cheat` is removed.

#### Not to try
Do not use this audit to fix unrelated cheats elsewhere in the file.

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
