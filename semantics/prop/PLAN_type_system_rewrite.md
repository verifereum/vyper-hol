# PLAN

## Structured Components

### C0: Task-local proof completion for remaining fresh-stack cheats
- Kind: `proof_completion_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk is lowered back to 2 after replacing stuck C0.4 with a low-risk branch-local decomposition. E0230 shows the old projected-helper use was wrong, but the maintainer clarification authorizes the replacement linear proof discipline and existing siblings are preserved.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.1, C0.2, C0.3, E0227, E0228, E0229, E0230

#### Progress note
C0.1--C0.3 remain valid completed work. E0230 is carried forward only as diagnostic evidence for replacing C0.4; it does not invalidate the whole C0 subtree.

#### Summary
- Continue the task-local proof completion inside `semantics/prop` only.
- Completed audit/raw-call helper/static boundary-probe work remains valid.
- Replace the failed C0.4 one-step projected-helper integration with a linear static-success proof.
- Downstream ExtCall/RawCall components remain preserved but blocked until C0.4 closes.
- No evaluator/semantics definitions may be changed.

#### Argument
The remaining task is proof completion, not semantics redesign. For ExtCall branches, argument evaluation has already produced a well-typed intermediate state and runtime-typed argument values. Error prefixes preserve state and yield non-type-error failures; success prefixes rely on `run_ext_call` account preservation and then hand the post-update state to the optional driver/tail proof. The critical invariant is that the optional driver IH is consumed only at the concrete post-call continuation where its generated prefix antecedent has already been discharged.

#### Definition design
No definitions outside `semantics/prop` are to be edited. The intended proof interface is local branch facts: runtime-typed argument destructors, `run_ext_call_accounts_well_typed`, `env_consistent_get_tenv`, and `extcall_after_state_update_tail_sound`. Generated-prefix theorem plumbing is a failure sign, not an acceptable interface.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Existing local helper theorems near `extcall_static_projected_*` may be reused. New helper theorems, if any, must be compact and task-local; the C0.4 proof itself should live in the existing `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` block.

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

### C0.4: Integrate ExtCall static branch with a branch-local success proof
- Kind: `mutual_resume_proof_subtree`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: Risk 2 after decomposition: E0230 invalidates the direct projected-helper application, but the source already contains proved static projected lemmas and the maintainer explicitly permits a careful linear proof that specializes the optional-driver IH only in the single concrete success-continuation branch.
- Dependencies: C0.3
- Supersedes: C0.4
- Progress transition: `replacement`
- Carries progress/evidence from: C0.3, E0229, E0230
- Invalidates prior progress/evidence: C0.4@old-leaf

#### Progress note
Carries C0.3/E0229 as evidence that the compact static helper theorem is mathematically sound, and E0230 as evidence that this helper cannot be applied directly from the live Resume boundary. The old C0.4 leaf strategy is invalidated and replaced by children C0.4.1--C0.4.4.

#### Summary
- Replace the failed one-step projected-helper integration with a branch-local static-success proof.
- Keep all work inside `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- Follow `extcall_static_projected_sound` as the semantic model.
- Specialize the generated optional-driver IH only after the concrete successful ExtCall continuation is reached.
- Remove the static-success `cheat` without broad generated-prefix cleanup.

#### Description
The prior plan assumed that `extcall_static_projected_state_well_typed` or `extcall_static_projected_sound` could be applied directly after `RESUME_TAC`; E0230 shows the live optional-driver IH remains behind a generated prefix implication. The replacement proof must proceed linearly through the ExtCall monadic chain, close error branches immediately, and then use the generated IH in the single success branch where all prefix facts are concrete.

#### Approach
Use the code around lines 17748--17776 and the proof of `extcall_static_projected_sound` as templates. Split `run_ext_call`, pair-destruct the result, split success/revert, perform account/transient updates, derive `accounts_well_typed` by `run_ext_call_accounts_well_typed`, derive `runtime_consistent env cx args_st`, evaluate `ret_type`, and close with `extcall_after_state_update_tail_sound`. For `drv = SOME _`, specialize the live generated implication only after these concrete prefix equations exist; for `drv = NONE`, avoid invoking `THE drv`.

#### Not to try
Do not retry `irule`, `MATCH_MP_TAC`, or `drule_all extcall_static_projected_state_well_typed` on the initial projection goal. Do not introduce a long generated-prefix adapter theorem. Do not use broad `gvs[AllCaseEqs()]`, broad `simp`, or top-level prefix mining to recover the driver premise.

#### Argument
The static ExtCall soundness argument is the same as the proved projected helper: runtime-typed arguments determine the target and calldata inputs; prefix errors are non-type-error failures; successful external calls preserve account well-typedness; post-call account/transient updates produce the state on which the optional driver runs. The optional driver IH is therefore a tail-continuation fact and should be instantiated at that continuation, not at the start of the Resume.

#### Definition design
No evaluator or semantics definition changes. The proof interface consists of small branch-local facts and existing helpers: `extcall_static_args_runtime_typed_dest`, `extcall_static_args_runtime_typed_nonempty`, `run_ext_call_accounts_well_typed`, `env_consistent_get_tenv`, and `extcall_after_state_update_tail_sound`. Failure sign: any need to restate the whole generated prefix as a named theorem or recover it by global simplification.

#### Code structure
Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Work in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` around line 17748. If a tiny helper is unavoidable, place it near the existing static ExtCall local helpers and keep its statement compact; do not edit outside `semantics/prop`.

### C0.4.1: Re-establish the static success branch prefix without using the projected helper
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: Risk 1: mechanical replay of existing prefix splits through calldata construction, empty-code check, and `run_ext_call`, preserving current suspended error branches and avoiding the failed helper application.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: E0230

#### Progress note
Refines the old C0.4 attempt by keeping the useful linear prefix structure while removing the invalid projected-helper application at the initial projection goal.

#### Summary
- Work in `Expr_Call_ExtCall_result_static_success`.
- Keep `RESUME_TAC`, condition rewrite, static argument destructor, and nonempty proof.
- Unfold the evaluator one operation at a time.
- Preserve existing calldata, empty-code, and run-failed suspended/error branches.
- End with a focused concrete `run_ext_call = SOME ...` success branch.

#### Approach
Start from the intentional baseline around lines 17748--17776. Replay the current prefix with exact `Cases_on` for `build_ext_calldata`, `NULL ...code`, and `run_ext_call`; do not apply `extcall_static_projected_state_well_typed`. The expected result is not a closed theorem yet, but a focused success branch ready for tail reasoning.

#### Not to try
Do not attempt to close `state_well_typed st'` before destructing the concrete successful `run_ext_call` result. Do not simplify the large generated IH assumption globally.

### C0.4.2: Derive static run-success preservation facts before optional driver use
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Risk 2: this follows the already-proved projected static helper tail, but must be transcribed carefully in the live Resume branch with generated names.
- Dependencies: C0.4.1

#### Summary
- In the `run_ext_call = SOME result` branch, destruct the returned tuple.
- Close revert/error cases immediately with exact rewrites.
- On success, prove `accounts_well_typed accounts'` using `run_ext_call_accounts_well_typed`.
- Establish `runtime_consistent env cx args_st` and `get_tenv cx = env.type_defs`.
- Prepare the post-update facts consumed by tail soundness.

#### Approach
Mirror the proof of `extcall_static_projected_sound`: `PairCases_on` the result, split success, rewrite `assert_def`, `update_accounts_def`, and `update_transient_def`, then derive account preservation with `drule_all run_ext_call_accounts_well_typed`. Use `well_formed_type_def`, `evaluate_type`, and `env_consistent_get_tenv` as in the helper proof.

#### Not to try
Do not call `extcall_static_projected_sound` here; its compact driver premise is not available in the live context. Do not manually instantiate generated prefix variables except later for the driver IH after the single success continuation is reached.

### C0.4.3: Specialize the generated optional-driver IH in the concrete static success continuation
- Kind: `proof_boundary_probe`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Risk 2: E0230 identified this as the mismatch, but the maintainer clarification explicitly allows this specialization after reaching the single concrete ExtCall success-continuation branch.
- Dependencies: C0.4.2
- Checkpoint: yes

#### Summary
- Derive a local compact driver theorem for `THE drv` only in the concrete success continuation.
- Match the driver premise needed by `extcall_after_state_update_tail_sound`.
- Specialize the live generated implication with concrete branch values and discharge already-split prefix equations.
- Handle `drv = NONE` separately.
- Checkpoint: stop if this requires broad prefix mining or a generated-prefix adapter theorem.

#### Statement
Local derived fact inside the Resume branch, under the branch condition where `IS_SOME drv`:
```
!env0 st0 res0 st0'.
  env_consistent env0 cx st0 /\ state_well_typed st0 /\
  context_well_typed cx /\ accounts_well_typed st0.accounts /\
  functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
  well_typed_expr env0 (THE drv) ==>
  state_well_typed st0' /\ env_consistent env0 cx st0' /\
  accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
  case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T
```

#### Approach
Case-split `drv` or expose `IS_SOME drv` only at the point where the driver is evaluated. In the `SOME` case, instantiate the generated implication with the actual prefix witnesses fixed by C0.4.1--C0.4.2 and discharge its antecedent with exact assumptions/equalities from the linear proof. Then use the resulting compact fact by ordinary `drule`/`disch_then` at the tail use site.

#### Not to try
Do not recover this fact at the top of the Resume. Do not use ASSUME-quoted copies of the whole generated prefix or a many-screen `qspecl_then` adapter theorem; if only that works, escalate.

### C0.4.4: Close the static ExtCall success cheat using tail soundness
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Risk 2: after C0.4.3 supplies the correct local driver interface, the remaining proof is the same tail closure already proved in `extcall_static_projected_sound`.
- Dependencies: C0.4.3
- Checkpoint: yes

#### Summary
- Invoke `extcall_after_state_update_tail_sound` in the final success branch.
- Supply state, environment, accounts, return-type, runtime-consistency, and driver facts from C0.4.2--C0.4.3.
- Close all projections of the mutual proof result.
- Remove the static-success `cheat` around line 17776.
- Build and grep to confirm C0.4 is no longer among remaining cheats.

#### Approach
Use the final block of `extcall_static_projected_sound` as the checklist: establish the conjunction by `irule extcall_after_state_update_tail_sound`, simplify concrete branch facts, and use the local driver IH from C0.4.3 only for the optional-driver subcase. After closure, run the task-local build and grep for `cheat`; expected remaining cheats should correspond only to downstream planned components.

#### Not to try
Do not finish by proving projection goals one-by-one with manual theorem plumbing. If `extcall_after_state_update_tail_sound` does not match after C0.4.3, stop and report the exact residual goal rather than broadening simplification.

### C0.5: Integrate ExtCall nonstatic branch and remove nonstatic cheat
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: Risk 2 because it mirrors the static proof with one additional amount argument; existing helpers `extcall_nonstatic_args_runtime_typed_dest`, `extcall_nonstatic_args_runtime_typed_nonempty`, and nonstatic projected lemmas cover the extra shape facts.
- Dependencies: C0.4
- Checkpoint: yes
- Carries progress/evidence from: C0.4

#### Progress note
New integration leaf for the remaining ExtCall nonstatic suspended result, expected to reuse the static continuation proof pattern.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` / remove the nonstatic ExtCall cheat.
- Derive both target address and amount from runtime-typed arguments.
- Use `build_ext_calldata ... (TL (TL vs))` and `run_ext_call ... (SOME amount)` branch structure.
- Reuse the same continuation helper shape as static after state/account/transient update.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  ...
QED
```

#### Approach
Follow the static proof but use `MAP expr_type es = BaseT AddressT :: BaseT (UintT 256) :: arg_types`, `extcall_nonstatic_args_runtime_typed_dest`, and `extcall_nonstatic_args_runtime_typed_nonempty`. In success branches, destruct `run_ext_call` to obtain `(success, returnData, accounts', tStorage')`, prove account typing, and call the same tail soundness lemma with `is_static = F`. Keep the optional-driver IH conditional and local to the return tail.

#### Not to try
Do not duplicate the entire static proof with generated variable plumbing. Do not unfold more evaluator layers than needed once the projected/tail helper applies.

### C0.6: Close RawCallTarget statement-expression soundness cheat
- Kind: `mutual_resume_proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: Risk 2: RawCallTarget is a single remaining expression-call branch and should be handled by the same branch-local evaluator discipline; if a missing compact helper appears, this component must stop as NEW_DEPENDENCY rather than producing theorem plumbing.
- Dependencies: C0.2, C0.5
- Checkpoint: yes
- Carries progress/evidence from: C0.2

#### Progress note
New proof-completion leaf for the RawCallTarget cheat; depends on raw-call return-type well-formedness if that fact is needed by the branch typing proof.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` / remove the RawCallTarget cheat.
- Use the same combined postcondition as ExtCall: state/env/accounts preservation, no-TypeError, and result typing together.
- Bring in `raw_call_return_type_well_formed` rather than reproving return-type well-formedness locally.
- Split raw-call evaluator branches linearly and close error cases immediately.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  ...
QED
```

#### Approach
Start by rewriting the relevant `well_typed_expr` call case once to expose typed arguments/flags and `raw_call_return_type` facts. Split argument evaluation and raw-call semantic operations at the point the evaluator branches; use branch facts and `raw_call_return_type_well_formed` for result typing. If the branch needs a reusable theorem, formulate a local RawCall projected helper whose conclusion is exactly the mutual postcondition, analogous to `extcall_*_projected_sound`.

#### Not to try
Do not unfold old retired type-soundness theories or use legacy `vyperTypeSoundnessScript` facts unless they are already imported and clearly fresh-stack compatible. Do not solve RawCall by weakening result typing or changing `raw_call_return_type_def`.

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
