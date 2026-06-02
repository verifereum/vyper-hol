# PLAN

## Structured Components

### C0: Finish task-scoped type-system rewrite proof integrity inside semantics/prop
- Kind: `proof_subtree_parent`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1 risk 3. C0.2.1's current plan asks to retry the same linear prefix-through-ExtCall proof shape that prior scoped episodes already closed as non-straightforward: E0108 reports this exact static success Resume linear prefix attempt timed out on >4KiB generated optional-driver prefix goals before reaching the tail; E0157 reconfirmed the current `Expr_Call_ExtCall_result_static_success` Resume still resumes to large pre-tail generated-prefix projection goals. The task explicitly says stop on unexpected/non-straightforward design issues, so repeating the same branch-by-branch proof would violate do-not-retry evidence.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, E0157, TO_type_system_rewrite-20260601T220715Z_m3232_t001

#### Progress note
Refines C0 only to repair canonical scheduling. No proof progress is invalidated; the prior C0.2 replacement remains the current proof strategy. The dependency edge C0.3 -> C0.2 was too weak for the scheduler because C0.2 is a parent/grouping component; downstream proof leaves now depend on C0.2.3, the terminal static-success validation leaf.

#### Summary
- Finish exactly the remaining type-system rewrite obligations inside `semantics/prop`.
- Static ExtCall success is the required immediate gate: C0.2.1, then C0.2.2, then C0.2.3.
- Nonstatic ExtCall C0.3 must not begin until C0.2.3 is done.
- RawCallTarget and final audit remain later work and are not re-designed by this update.
- No evaluator/semantics definitions may be changed, and no files outside `semantics/prop` may be edited.

#### Argument
The subtree is a sequence of local proof repairs for remaining `semantics/prop` soundness obligations. The static ExtCall generated-driver mismatch must be resolved first because the nonstatic branch is intended to reuse the same linear continuation proof interface. Parent components are grouping/context only; scheduler-critical dependencies must therefore point at terminal leaf checkpoints such as C0.2.3, not just at parent C0.2.

#### Definition design
No semantic definitions are to be changed. Proof interfaces should expose small monadic-tail obligations at concrete success branches and consume existing continuation helpers there. Scheduling is part of the proof interface: C0.3 may use the static proof shape only after C0.2.3 has validated that the static branch actually closes without forbidden prefix plumbing.

#### Code structure
All edits stay in `semantics/prop`, primarily `vyperTypeStmtSoundnessScript.sml`. This update changes PLAN metadata only: proof code should next edit the static ExtCall success Resume and any tiny local helper near the existing ExtCall continuation helpers. Do not edit source for C0.3 until C0.2.3 is complete.

### C0.1: Refactor static ExtCall Resume into a branch-local suspended success continuation
- Kind: `proof_architecture_probe`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: This is the de-risking step for the former blocker. It changes only proof structure and has a clear pass/fail criterion: all static ExtCall prefix/error branches are discharged, and exactly the concrete success-continuation branch is suspended with the generated optional-driver IH and concrete prefix facts in context.
- Checkpoint: yes
- Supersedes: C0.2.1.3.3, C0.2.1.3.3.4
- Progress transition: `replacement`
- Carries progress/evidence from: E0149, E0155
- Invalidates prior progress/evidence: terminal static ExtCall no-frontier scheduling status

#### Progress note
Prior failed attempts are carried forward as negative evidence identifying the bad interface. This component replaces that interface with a branch-local suspended subgoal.

#### Summary
- Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- Replace the explicit static ExtCall `cheat` with a Resume body that follows the evaluator prefix linearly.
- Close expression-error, calldata-error, missing-code, revert, and other failure branches immediately.
- At the single success-continuation branch, use `suspend "Expr_Call_ExtCall_result_static_success"` or an equivalent local name.
- Build the target theory to confirm the remaining obligation is the intended suspended success subgoal, not a broad top-level prefix goal.

#### Statement
Proof-architecture checkpoint at the existing Resume site for `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`. The Resume body must reduce all static ExtCall cases except the final success-continuation branch, which is deliberately suspended with local branch context.

#### Approach
Unfold `evaluate_def` only as needed for `Call ... (ExtCall T ...)`, then split the monadic prefix one operation at a time. Use the expression-list IH and static ExtCall argument destructors only after the expression-list success case. For failing branches, immediately close with local rewrites such as `bind_def`, `return_def`, `raise_def`, `assert_def`, and `no_type_error_result_def`; keep only one success path alive.

#### Not to try
Do not unfold/simplify the entire ExtCall prefix with `AllCaseEqs()` or broad `gvs`. Do not prove the success tail inline here. Do not instantiate the generated optional-driver IH before the concrete success-continuation branch exists.

### C0.2: Close static ExtCall success via semantic boundary helpers, not generated-prefix replay
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The stuck evidence invalidates the previous linear Resume-prefix strategy, but the source already contains a natural semantic boundary (`extcall_static_projected_state_well_typed`) proving the state projection from the ordinary static ExtCall evaluation and argument-result facts. Extending that boundary to the full postcondition and using it in the Resume avoids the >4KiB generated prefix adapter shape.
- Dependencies: C0.1
- Supersedes: C0.2@prior, C0.2.1@E0158, E0157
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1, E0156, TO_type_system_rewrite-20260601T220715Z_m3225_t001, TO_type_system_rewrite-20260601T220715Z_m3227_t001
- Invalidates prior progress/evidence: C0.2.1@prior-linear-prefix-strategy, E0158

#### Progress note
Keeps the C0.1 localized static-success Resume and E0157/E0158 goal-shape diagnosis, but replaces the proof strategy. Prior evidence that the Resume exposes large generated-prefix goals now guides what not to do rather than supporting the old leaf.

#### Summary
- Static ExtCall success remains the immediate required gate.
- Do not retry `RESUME_TAC` plus step-by-step replay of the generated ExtCall prefix.
- Introduce/use semantic boundary helpers stated over the ordinary `eval_expr` ExtCall equation plus `eval_exprs` success facts.
- Close the optional-driver generated premise by specializing the driver IH after assuming `returnData = []` and `IS_SOME drv`; ignore prefix facts except those branch facts.
- Then close result projections in the Resume by applying the static semantic boundary helper.
- Downstream nonstatic ExtCall remains blocked until this subtree builds without the static success cheat.

#### Description
The previous C0.2 plan assumed that the suspended static-success branch could be moved linearly through `build_ext_calldata`, account lookup, `run_ext_call`, success check, and updates. E0108/E0157/E0158 show that this exposes generated optional-driver prefix implications before reaching a useful tail. The new boundary is not a generated-prefix adapter: it is a reusable semantic lemma about the whole static ExtCall `eval_expr` result under the already-known argument evaluation success and the driver IH premise.

#### Approach
First prove a full static ExtCall projected-soundness lemma by generalizing the already proved `extcall_static_projected_state_well_typed` proof body to return the whole conjunction, using `extcall_after_state_update_tail_sound` or `extcall_success_continuation_sound_cond_driver_ih` at the success tail. Then use this lemma in the Resume after `RESUME_TAC`. Treat any need to copy the long quantified generated prefix into a theorem statement as a stop condition.

#### Not to try
Do not replay the generated prefix inside the Resume. Do not create a theorem whose assumptions are the long `∀s'' vs ... update_transient ...` generated implication. Do not use broad `gvs`/`AllCaseEqs()` over the whole static ExtCall prefix to recover the driver premise.

#### Argument
The static ExtCall branch has two obligations the old plan conflated. The optional-driver obligation is independent of the monadic prefix once `returnData = []` and `IS_SOME drv` are assumed: discharge it from the driver subexpression IH and `well_typed_opt env drv`, not by simplifying calldata/account/update operations. The result projection obligations are semantic properties of the whole static ExtCall evaluation after `eval_exprs` succeeds; discharge them by a boundary lemma whose statement mentions the ordinary evaluator equation and argument-success facts, not the generated suspension prefix. This mirrors `extcall_static_projected_state_well_typed` but returns the full postcondition needed by the mutual theorem.

#### Definition design
No evaluator or semantic definitions change. The key proof interface is a local theorem near existing ExtCall helpers with the same natural assumptions as `extcall_static_projected_state_well_typed` but conclusion `state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\ result-typed case`. Failure signs: the helper statement mentions generated variables such as `s''`, `s'³'`, `t'¹¹'`, or a long prefix implication; or its consumer must unfold the whole prefix instead of using `irule`/`drule_all`.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Add the new full static projected helper adjacent to `extcall_static_projected_state_well_typed` around the existing ExtCall helper block, not inside the Resume. Then edit only `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` near the localized cheat. Do not edit evaluator/semantics definitions or files outside `semantics/prop`.

### C0.2.1: Add full static ExtCall projected-soundness boundary lemma
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: This is a standard strengthening of an already present local lemma: `extcall_static_projected_state_well_typed` proves the state projection and its proof internally derives the full conjunction before simplifying. The new lemma exposes that full conjunction as the reusable boundary needed by the Resume.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: C0.2.1@prior
- Progress transition: `replacement`
- Carries progress/evidence from: extcall_static_projected_state_well_typed, E0158
- Invalidates prior progress/evidence: C0.2.1@prior-linear-prefix-leaf

#### Progress note
Replaces the stuck linear-prefix leaf with a semantic helper leaf. E0158 remains valid evidence that the old leaf should not be retried.

#### Summary
- Prove a local helper for the full static ExtCall result postcondition.
- Use the same assumptions as `extcall_static_projected_state_well_typed`, including the whole `eval_expr` equation, `eval_exprs` success, runtime typing of argument values, and the driver IH premise.
- The conclusion must be the complete conjunction needed for expression soundness, not only `state_well_typed st'`.
- The proof may reuse/generalize the existing state-projection proof body.
- This helper is a checkpoint because it validates the replacement boundary.

#### Statement
Add near the ExtCall helper block:
```sml
Theorem extcall_static_projected_sound[local]:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\ MAP expr_type es = BaseT AddressT::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
       accounts_well_typed st0.accounts /\ functions_well_typed cx /\
       eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st' /\ env_consistent env cx st' /\
        accounts_well_typed st'.accounts /\ no_type_error_result res /\
        case res of
        | INL tv => expr_result_typed env (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) tv
        | INR _ => T
```

#### Approach
Copy the structure of `extcall_static_projected_state_well_typed`, but keep the full conjunction established near the tail instead of ending with `simp[]` for only the state projection. Use `extcall_static_args_runtime_typed_dest` and `extcall_static_args_runtime_typed_nonempty` for argument inversion, rewrite the single ordinary `eval_expr` equation with the known `eval_exprs` success, and at the successful `run_ext_call`/non-reverted branch use `run_ext_call_accounts_well_typed` plus `extcall_after_state_update_tail_sound` or `extcall_success_continuation_sound_cond_driver_ih`.

#### Not to try
Do not state this helper over the generated Resume prefix variables. Do not add a long adapter theorem whose assumptions are the quantified suspended implication. Do not broaden the helper to nonstatic ExtCall in this leaf; keep it static and match the immediate use site.

### C0.2.2: Close static Resume driver-premise subgoal without prefix replay
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: The generated premise shown after `RESUME_TAC` is a driver IH obligation guarded by `returnData = [] /\ IS_SOME drv`; it should be proved by stripping the guard/prefix assumptions and specializing the optional-driver/subexpression IH, not by simplifying any ExtCall prefix operation.
- Dependencies: C0.2.1
- Supersedes: C0.2.1@prior-driver-prefix-work
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T220715Z_m3227_t001
- Invalidates prior progress/evidence: C0.2.1@prior-linear-prefix-leaf

#### Progress note
Uses E0157/E0158 evidence to focus only on the generated driver-premise subgoal and avoid the prefix split that made the old proof non-straightforward.

#### Summary
- Edit the static-success Resume after the new helper exists.
- Run `RESUME_TAC` only to expose the small set of projection/premise goals.
- For the generated optional-driver premise, strip assumptions, use `IS_SOME drv` to case/analyze `drv`, obtain `well_typed_expr env (THE drv)` from `well_typed_opt env drv`, and specialize the available driver IH.
- This proof must not inspect `build_ext_calldata`, accounts, `run_ext_call`, or updates.
- Leave projection goals for C0.2.3 if they are not closed in the same compact script.

#### Statement
Refactor part of:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]:
  ...
QED
```
Milestone: the optional-driver generated premise closes without unfolding the ExtCall monadic prefix.

#### Approach
After `RESUME_TAC`, identify the subgoal shaped like `∀s'' vs ... . prefix ∧ returnData = [] ∧ IS_SOME drv ==> ∀env st res st'. ... eval_expr cx (THE drv) ... ==> ...`. Prove it by `rpt strip_tac`, case-splitting `drv`, simplifying `well_typed_opt`, and applying the driver expression IH already in the mutual proof context. The long prefix assumptions should remain unused except for the branch facts already stripped.

#### Not to try
Do not call `gvs[AllCaseEqs()]` or simplify the static ExtCall evaluator prefix in this subgoal. Do not manually instantiate a lemma with all generated prefix variables. If no driver IH is available after `RESUME_TAC`, stop and escalate with the exact context rather than rebuilding the prefix proof.

### C0.2.3: Use static projected-soundness helper to finish the static success Resume and remove cheat
- Kind: `main_proof`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: Once C0.2.1 provides the full semantic boundary and C0.2.2 discharges the generated driver premise, the remaining projection goals should match the helper's conclusion and close by `irule`/`drule_all` using existing assumptions from the resumed branch.
- Dependencies: C0.2.2
- Checkpoint: yes
- Supersedes: Expr_Call_ExtCall_result_static_success_cheat
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1, C0.2.1, C0.2.2
- Invalidates prior progress/evidence: C0.2.3@prior-tail-only-audit

#### Progress note
This is the terminal static-success validation leaf for the replacement subtree. It removes the localized cheat introduced by C0.1 using the new boundary rather than the invalidated prefix traversal.

#### Summary
- Finish `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`.
- Apply `extcall_static_projected_sound` to result-projection goals produced by `RESUME_TAC`.
- Use existing assumptions: env/state/context/account/function well-typedness, static `MAP expr_type`, `eval_exprs` success facts, and `exprs_runtime_typed` from the argument IH.
- The proof should be short and helper-driven.
- Verify `vyperTypeStmtSoundnessTheory` builds and the static success `cheat` is gone.

#### Statement
Complete and build:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]:
  ... no cheat ...
QED
```
Expected verification: `holbuild` target `vyperTypeStmtSoundnessTheory` succeeds with no remaining cheat in this Resume.

#### Approach
For projection goals such as `state_well_typed st'`, `env_consistent env cx st'`, `accounts_well_typed st'.accounts`, `no_type_error_result res`, or the result-typed case, apply `extcall_static_projected_sound` and simplify/select the needed conjunct. Use the argument-evaluation IH already specialized in the Resume context for `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, and `exprs_runtime_typed env es vs`. Keep the script local and avoid unfolding the ExtCall prefix except as already encapsulated by the helper.

#### Not to try
Do not re-open the monadic prefix manually if `irule extcall_static_projected_sound` does not immediately match; first adjust the helper statement to the actual projection-goal shape. Do not prove projections one by one by copied evaluator splitting. Do not start C0.3 until this checkpoint is accepted.

### C0.3: Close the nonstatic ExtCall result branch using the same linear continuation interface
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The proof remains standard analogous work, but it is intentionally blocked until the static proof interface is validated by C0.2.3. Depending on parent C0.2 was too weak for the scheduler; the terminal static child is now the dependency.
- Dependencies: C0.2.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.3

#### Progress note
Only scheduling/dependency metadata changed. The nonstatic proof strategy remains unchanged and should begin only after the static success checkpoint completes.

#### Summary
- Do not begin until C0.2.3 is done.
- Work at the existing nonstatic ExtCall Resume site.
- Mirror the validated static proof shape, adjusted for the nonstatic amount/value argument and `SOME amount` external call.
- Keep optional-driver IH use local to the concrete success branch.
- Close the nonstatic ExtCall cheat without global generated-prefix cleanup.

#### Statement
Close the nonstatic `eval_all_type_sound_mutual[Expr_Call_ExtCall_result...]` Resume obligation for external calls whose first runtime argument supplies the call amount, preserving the theorem's existing source statement.

#### Approach
After C0.2.3, use the static proof as a template. Split the evaluator prefix linearly, use nonstatic runtime-typed argument destructors to expose target/value/argument-list facts, and apply the ExtCall continuation helper only after the successful concrete prefix has established updated accounts/transient state and driver facts.

#### Not to try
Do not bypass the static gate. Do not resurrect the old compact-boundary/direct-consumer plan if it requires prefix reconstruction. Do not use global `AllCaseEqs()` cleanup over the whole nonstatic ExtCall expression-call prefix.

### C0.4: Prove RawCallTarget expression-call soundness through local tail boundaries
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 3
- Work units: 0
- Rationale: RawCallTarget was already decomposed into finite local boundary obligations and is independent of the static generated-driver mismatch. The required work is standard: argument destructors, flag-dependent return typing, one monadic tail boundary, and a Resume replacement analogous to existing send/raw-log branches.
- Dependencies: C0.3
- Supersedes: C0.3, C0.4
- Progress transition: `replacement`
- Carries progress/evidence from: E0106
- Invalidates prior progress/evidence: duplicated legacy RawCallTarget component split

#### Progress note
This flattened RawCallTarget parent consolidates the duplicate C0.3/C0.4 plans from the stale subtree and keeps only the durable semantic obligations.

#### Summary
- Add/retain RawCallTarget argument destructors matching the Resume use site.
- Prove flag-dependent return value typing for `raw_call` result shapes.
- Package account/transient updates, no-TypeError, and result typing in one monadic tail boundary.
- Replace the RawCallTarget Resume body with prefix split plus boundary-helper application.
- Build/audit locally before the final zero-cheat audit.

#### Description
This parent owns the RawCallTarget proof work after ExtCall is fixed. The child helpers should make the final Resume proof boring: the consumer should not unfold the whole raw-call tail repeatedly.

#### Approach
Prove children in order. Use existing send/raw-log helper statements as interface models, but phrase conclusions to match the RawCallTarget Resume goal directly via `irule`/`drule`. The final Resume proof should expose typed arguments, split the monadic prefix to the tail, and apply the tail boundary.

#### Not to try
Do not prove RawCallTarget by a large inline monadic proof at the Resume site. Do not duplicate helper families with slightly different conclusions; if the use site does not match, adjust the boundary statement before proceeding.

#### Argument
RawCallTarget soundness is a finite branch proof, not an induction/driver-IH problem. Well-typedness constrains the runtime argument list and flag-dependent return shape. The evaluator tail can only raise explicit runtime/assertion errors or return a value whose type is determined by `raw_call` flags; account/transient mutations preserve account and state typing via existing preservation lemmas. Packaging these facts in a tail boundary lets the Resume proof focus on evaluator prefix alignment.

#### Definition design
No definitions change. The boundary interface should expose: (1) RawCallTarget runtime argument inversion, (2) return-value typing by `rcf_revert_on_failure` and `rcf_max_outsize`, and (3) monadic tail soundness from concrete branch facts. Failure sign: the Resume proof repeatedly unfolds raw-call tail internals or requires manual construction of large conjunction theorems.

#### Code structure
Place RawCallTarget local helper theorems beside nearby expression-call helper blocks in `vyperTypeStmtSoundnessScript.sml`. Keep helper names RawCallTarget-specific and local unless already intended for reuse. The Resume replacement belongs at the existing RawCallTarget suspended/cheated branch site.

### C0.4.1: Derive RawCallTarget runtime argument destructors
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: This is list-shape and value-typing inversion analogous to existing send/raw-log/ExtCall destructors.
- Dependencies: C0.3
- Supersedes: C0.3.1, C0.4.1
- Progress transition: `replacement`

#### Progress note
Consolidates duplicate legacy RawCallTarget destructor leaves into one use-site-matched boundary lemma.

#### Summary
- Prove destructors for the RawCallTarget runtime argument list required by the evaluator branch.
- Conclusions should name the concrete target/value/data/default facts the Resume proof needs.
- Match existing `send_args_runtime_typed_dest`/raw-log/ExtCall destructor style.
- Keep the theorem local if no other script needs it.

#### Statement
A local theorem (or small theorem pair) destructing the RawCallTarget `exprs_runtime_typed`/well-typed-args assumptions into the concrete runtime values and typing facts needed by the RawCallTarget Resume branch. Use the exact constructor/argument names from the existing source branch.

#### Approach
Use list case analysis and simplification of the relevant runtime-typed argument definitions. Split only as far as needed to expose the target address, call data/value/default argument facts, and value typing assumptions used downstream.

#### Not to try
Do not leave the final Resume proof to destruct long nested list/typing assumptions manually. Do not formulate a generic destructor if a RawCallTarget-specific one matches the use site better.

### C0.4.2: Prove flag-dependent RawCallTarget return value typing
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: Finite case analysis over RawCallTarget flags and return-shape definitions; no generated IH or induction risk.
- Dependencies: C0.4.1
- Supersedes: C0.3.2, C0.4.2
- Progress transition: `replacement`

#### Progress note
Consolidates duplicate legacy return-typing leaves and keeps the flag case split as a reusable boundary.

#### Summary
- Prove the runtime typing of the value returned by RawCallTarget for each flag combination.
- Split on `flags.rcf_revert_on_failure` and `flags.rcf_max_outsize = 0` as required by the source definitions.
- Use existing value typing and raw-call return type well-formedness lemmas if visible.
- Phrase the conclusion so the tail boundary can consume it directly.

#### Statement
A local theorem giving the `expr_result_typed`/`value_runtime_typed` fact for the RawCallTarget return value under the well-typed RawCallTarget flag/return-type assumptions present in the Resume branch.

#### Approach
Perform finite case splits over the relevant RawCallTarget flags, then simplify the return-value constructors and value typing definitions. Keep hypotheses close to the branch context; avoid proving a more abstract theorem that later requires manual instantiation.

#### Not to try
Do not solve this by a huge `metis_tac` over all value-typing definitions. If the theorem is hard to apply later, strengthen/reshape its conclusion before continuing.

### C0.4.3: Prove RawCallTarget monadic tail soundness boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: This packages the missing interface identified by prior work: side-effect preservation, no-TypeError, and result typing for the already-split RawCallTarget tail from concrete branch facts.
- Dependencies: C0.4.2
- Checkpoint: yes
- Supersedes: C0.3.3, C0.4.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0106

#### Progress note
Carries forward the diagnosis that RawCallTarget needs a tail boundary, but replaces duplicate legacy components with a single use-site-matched helper.

#### Summary
- Prove one tail helper for the RawCallTarget monadic operations after arguments are known.
- Inputs should be concrete branch facts, account/state well-typedness, and the destructor facts from C0.4.1.
- Outputs should cover no-TypeError, state/account preservation, and result typing needed by the Resume branch.
- Use C0.4.2 for return value typing and existing account/transient preservation lemmas for state side effects.

#### Statement
A local RawCallTarget tail-soundness theorem whose hypotheses match the concrete post-argument-split branch facts and whose conclusion matches the final conjunction/projection required by the RawCallTarget Resume proof.

#### Approach
Split the raw-call monadic tail one operation at a time. Close error branches with local `no_type_error_result_def` rewriting, use existing account/transient preservation lemmas after updates, and use C0.4.2 for the success result shape. Keep the theorem consumer-oriented: the final Resume proof should apply it without reconstructing a large prefix.

#### Not to try
Do not put this entire proof inline in the Resume. Do not require the final consumer to manually assemble a theorem with `MATCH_MP`/`CONJ` plumbing.

### C0.4.4: Replace RawCallTarget Resume body with boundary-helper proof
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 3
- Work units: 3
- Rationale: With the RawCallTarget boundary lemmas available, the Resume proof is standard prefix splitting plus helper application analogous to nearby expression-call branches.
- Dependencies: C0.4.3
- Checkpoint: yes
- Supersedes: C0.3.4, C0.3.5, C0.4.4
- Progress transition: `replacement`
- Invalidates prior progress/evidence: legacy duplicated RawCallTarget audit leaf

#### Progress note
Combines final proof replacement and local audit for RawCallTarget because the boundary lemmas should make the build check mechanical.

#### Summary
- Edit the existing RawCallTarget Resume/cheat site only.
- Split the evaluator prefix to the concrete RawCallTarget tail.
- Use C0.4.1 destructors and C0.4.3 tail boundary; avoid repeated tail unfolding.
- Build the target theory and verify the RawCallTarget cheat/suspension is removed.

#### Statement
Close the existing RawCallTarget expression-call soundness Resume obligation in `eval_all_type_sound_mutual`, preserving the theorem's source statement.

#### Approach
Follow surrounding successful expression-call Resume proofs. After expression-list success and well-typed-branch inversion, invoke the RawCallTarget destructors and then the tail boundary. Error branches should close immediately by no-TypeError rewrites or existing IH/preservation facts.

#### Not to try
Do not leave stale `suspend`/`cheat` artifacts around RawCallTarget after the proof builds. Do not stage unrelated task-memory or untracked artifacts with the proof edit.

### C0.5: Task-scoped proof-integrity audit and unsigned commit
- Kind: `integration_validation`
- Risk: 1
- Work priority: 90
- Work units: 1
- Rationale: Final validation and commit hygiene are mechanical after all proof leaves complete. This component must be blocked until the RawCallTarget terminal proof leaf is done.
- Dependencies: C0.4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.5

#### Progress note
Scheduling metadata retained/clarified so the final audit cannot run before proof leaves complete.

#### Summary
- Run the task-scoped audit only after C0.4.4 and all earlier proof leaves are done.
- Verify no task-scoped cheats/suspends remain in the target proof obligations.
- Ensure edits are confined to `semantics/prop`.
- Commit progress explicitly without GPG signing.

#### Statement
Final task-scoped validation and unsigned commit for the completed `semantics/prop` type-system rewrite proof work.

#### Approach
Build the relevant `semantics/prop` theory, grep the edited regions for `cheat`/stale `suspend`, and check `git diff --stat`/`git status` for path scope. Commit with GPG signing disabled, e.g. using a command-line option/config that explicitly prevents signing.

#### Not to try
Do not audit or commit unrelated repository cleanup. Do not use a signed commit path that may prompt for a GPG password.
