# PLAN

## Structured Components

### C0: Type-system rewrite proof completion
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.1.2 risk 3. The quarantined static-prefix proof is build-clean with a tail cheat, but the required low-risk success-tail interface failed: neither `irule driver_ih` nor `match_mp_tac driver_ih` can match the captured generated optional-driver theorem to the compact conditional premise of `extcall_success_continuation_sound_cond_driver_ih`. Proceeding would require a manual full-prefix instantiation or generated-prefix adapter, which the PLAN forbids.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0

#### Progress note
Parent included only to satisfy dotted-component context for the local subtree merge.

#### Summary
Parent context for the task-scoped type-system rewrite proof. This update is limited to the ExtCall_result proof interface and does not authorize edits outside `semantics/prop`.

### C0.1: Prove `raw_call_return_type_well_formed` in the builtins theory
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: The theorem is already present and most cases are discharged before the single cheat. The remaining obligation is local arithmetic/type-shape reasoning about `raw_call_return_type`; it is independent of ExtCall_result and is a strict prerequisite for a clean RawCallTarget proof.
- Checkpoint: yes
- Progress transition: `refinement`
- Invalidates prior progress/evidence: C0.8

#### Progress note
This replaces old C0.8 under the flattened plan with the same obligation and no changed statement.

#### Summary
Remove the cheat in `semantics/prop/vyperTypeBuiltinsScript.sml` at `raw_call_return_type_well_formed`. Keep the theorem statement unchanged. Prove the remaining arithmetic/type-slot case locally. Build the relevant builtins theory after the proof. This proof must stay inside `semantics/prop`.

#### Statement
`Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)`

#### Approach
Continue from the existing proof skeleton after `Cases_on flags` and rewriting `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`. The existing `word_size_le` lemma is the intended arithmetic boundary; use it to control the `word_size n` branch and close the remaining slot-size/numeric side condition with targeted arithmetic, not by changing definitions. After replacing the cheat, build the theory that contains `vyperTypeBuiltinsScript.sml`.

#### Not to try
Do not change `raw_call_return_type`, `type_slot_size`, or ABI-size definitions. Do not move this proof outside `semantics/prop`. Do not leave the arithmetic case as a new helper unless it is a genuinely reusable one-line numeric lemma; the expected proof is local.

### C0.2: ExtCall type-soundness proof work
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.1.2 risk 3. The quarantined static-prefix proof is build-clean with a tail cheat, but the required low-risk success-tail interface failed: neither `irule driver_ih` nor `match_mp_tac driver_ih` can match the captured generated optional-driver theorem to the compact conditional premise of `extcall_success_continuation_sound_cond_driver_ih`. Proceeding would require a manual full-prefix instantiation or generated-prefix adapter, which the PLAN forbids.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2

#### Progress note
Parent included only for local subtree context; sibling obligations are not rewritten by this review.

#### Summary
ExtCall proof subtree. The key repair is local theorem quarantine, not evaluator-definition changes or generated-prefix adapter resurrection.

### C0.2.1: Quarantine generated ExtCall driver IH and prove ExtCall_result branches
- Kind: `proof_refactor`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.1.2 risk 3. The quarantined static-prefix proof is build-clean with a tail cheat, but the required low-risk success-tail interface failed: neither `irule driver_ih` nor `match_mp_tac driver_ih` can match the captured generated optional-driver theorem to the compact conditional premise of `extcall_success_continuation_sound_cond_driver_ih`. Proceeding would require a manual full-prefix instantiation or generated-prefix adapter, which the PLAN forbids.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.1, E0111
- Invalidates prior progress/evidence: C0.2.1.1.2@previous

#### Progress note
Carries forward the overall ExtCall_result goal but replaces the failed live-assumption tactic discipline evidenced by E0111.

#### Summary
- Repair the ExtCall_result proof interface after E0111.
- The generated optional-driver IH must not be a live simplifier assumption during prefix splitting.
- Capture it into an ML theorem variable with `qpat_x_assum ... (fn driver_ih => ...)`.
- Reapply it only in the concrete success-continuation branch.
- Do not revive generated-prefix adapter theorems or edit outside `semantics/prop`.

### C0.2.1.1: Prove ExtCall expression result soundness with branch-local native driver-IH specialization
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The previous compact conditional helper interface is invalidated by E0114, but the hard prefix hazard is now de-risked: E0113/E0114 show `pop_last_assum` quarantines the generated IH and the static prefix/error branches build with only the success tail cheated. The remaining strategy is standard but precise: after reaching the single success-continuation branch, specialize the captured generated IH in its native full-prefix shape using the live prefix equations, then project the expression-result conjunct needed by the existing tail helper. This is permitted by the maintainer clarification and avoids broad simplification or persistent adapter theorems.
- Progress transition: `replacement`
- Carries progress/evidence from: E0110, E0112, E0113, E0114
- Invalidates prior progress/evidence: C0.2.1.1@previous, C0.2.1.1.2@previous, C0.2.1.1.3@previous

#### Progress note
Carries forward the cleanup and the validated quarantine/prefix skeleton. Replaces only the failed compact-premise consumption interface; E0114's No-match evidence is accepted and used to change the proof boundary for both static and nonstatic result branches.

#### Summary
- Keep the generated optional-driver IH out of assumptions during evaluator-prefix splitting with `pop_last_assum (fn driver_ih => ...)`.
- Do not ask HOL matching to turn the native generated full-prefix IH into the compact conditional premise automatically; E0114 proves that interface does not match.
- At the single success-continuation branch, locally specialize the captured `driver_ih` with the live prefix equations and project the expression-result half.
- Reuse existing tail soundness lemmas after deriving the driver premise; do not resurrect generated-prefix adapter artifacts.

#### Approach
Treat captured `driver_ih` as a native full-prefix theorem. Use it only after the success case is selected and the driver path premise `returnData = [] /\ IS_SOME drv` is current. Specialize it with the concrete prefix variables/equations already in the branch, prove the generated prefix antecedent by live equalities and narrow monadic rewrites, and project the first conjunct.

#### Not to try
- Do not use `irule driver_ih` or `match_mp_tac driver_ih` directly for the compact premise; E0114 showed both fail.
- Do not resurrect `extcall_generated_driver_ih_def`, `extcall_generated_driver_ih_elim_expr`, or any named long generated-prefix adapter theorem.
- Do not leave the generated IH in assumptions while simplifying the evaluator prefix.
- Do not use broad `simp`/`gvs`, `AllCaseEqs()`, or broad `qpat_x_assum` patterns over the full ExtCall prefix.

#### Argument
The ExtCall_result branch has two proof phases. First, split the concrete evaluator prefix linearly while the huge generated optional-driver IH is quarantined as an ML theorem value, so ordinary rewriting does not traverse it. E0113/E0114 validate this phase for the static branch: target extraction, calldata construction, missing-code error, failed-run error, and revert error all close with narrow monadic rewrites when the raw IH is absent from assumptions.

Second, in the success branch only, the evaluator prefix has already produced concrete equations for every operation in the generated optional-driver IH antecedent: `eval_exprs`, target checks, calldata construction, account/transient reads, `run_ext_call`, success check, and account/transient updates. Consume the generated IH in that native implication shape. Its conclusion is stronger than the tail helper needs: it gives the expression-result soundness conjunct plus an additional place-expression conjunct. Project the expression conjunct and use it to satisfy the driver premise of `extcall_success_continuation_sound_cond_driver_ih`.

This avoids a separate generated-prefix adapter theorem. The only full-prefix reasoning is branch-local, after all prefix equations have concrete names and after all error branches have been discharged. If specialization still requires broad `gvs`, `AllCaseEqs`, or moving the generated IH back into assumptions before prefix splitting, stop again.

#### Definition design
No evaluator or semantics definitions may change. The proof interface for this subtree is boundary-theorem/tactic based:

- `extcall_static_args_runtime_typed_dest` and `extcall_static_args_runtime_typed_nonempty` remain the boundary for extracting the static target address and nonempty argument list from `exprs_runtime_typed`.
- `extcall_success_continuation_sound_cond_driver_ih` may still be used for the post-`run_ext_call` tail, but its compact driver premise must be supplied by a local native specialization of `driver_ih`, not by `irule driver_ih`/`match_mp_tac driver_ih` directly.
- The nonstatic branch uses `extcall_nonstatic_args_runtime_typed_dest` and then follows the same native-specialization interface.
- Failure signs: reintroducing `extcall_generated_driver_ih`, proving a named long prefix adapter, leaving `driver_ih` live while simplifying the prefix, or broad `AllCaseEqs()`/whole-prefix `gvs` before success-branch isolation.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and plan/state markdown under `semantics/prop`. Keep helper theorems local near the existing ExtCall helper block. Do not edit evaluator/semantics files. The generated-prefix adapter artifacts deleted in earlier episodes must remain absent. If a small local tactic idiom is needed to specialize `driver_ih`, keep it inline inside the relevant Resume proof rather than adding a global theorem whose statement mirrors the generated prefix.

### C0.2.1.1.1: Keep obsolete generated-prefix ExtCall driver artifacts removed
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed and build-checked; the replacement subtree still depends on not reviving the deleted adapter route.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0110, E0112, C0.2.1.1.1@previous

#### Progress note
No new work. Prior audit/build evidence remains applicable because the new plan also forbids these artifacts.

#### Summary
- Preserve prior deletion of generated-prefix adapter artifacts.
- Audit evidence already showed no `extcall_generated_driver_ih` references remain.
- This cleanup remains a dependency because stale adapter code would invite the forbidden route.

#### Approach
No edit needed unless the artifacts have reappeared. If checking, grep only within `semantics/prop` for `extcall_generated_driver_ih` and confirm the theory still builds after proof changes.

#### Not to try
Do not recreate these definitions as a shortcut for C0.2.1.1.2 or C0.2.1.1.3.

### C0.2.1.1.2: Static ExtCall_result branch using branch-local native driver-IH specialization
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: The static prefix and error cases are already validated with the `pop_last_assum` quarantine. The remaining success-tail issue is now decomposed to branch-local native specialization of the captured generated theorem, which the maintainer clarification permits after the concrete success branch is reached. Risk is standard provided the proof does not attempt automatic `irule` matching against the compact premise.
- Dependencies: C0.2.1.1.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0113, E0114, C0.2.1.1.2@previous
- Invalidates prior progress/evidence: C0.2.1.1.2@previous:compact-driver-premise-interface

#### Progress note
Accepts E0114 as a real interface failure. Carries forward the build-clean quarantine skeleton with a tail cheat, but replaces the failed `irule driver_ih`/`match_mp_tac driver_ih` step by branch-local specialization of the native generated IH.

#### Summary
- Finish `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`.
- Keep the existing `pop_last_assum (fn driver_ih => ...)` structure.
- Preserve the linear prefix/error-case proof that already builds with a success-tail cheat.
- In the `run_ext_call` success branch, derive the driver-expression soundness premise by specializing `driver_ih` in its native prefix shape and projecting the expression-result conjunct.
- Build `vyperTypeStmtSoundnessTheory` after removing the tail cheat.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]:
  (* prove the static ExtCall result branch of the mutual type soundness theorem, replacing the current success-tail cheat *)

#### Approach
Start from the current build-clean partial proof with the success-tail cheat. In the success branch, after proving the concrete returned accounts are well typed and stripping the final evaluator equality, use `extcall_success_continuation_sound_cond_driver_ih` for the tail. Prove its conditional driver premise by a local assertion: assuming `returnData = [] /\ IS_SOME drv`, specialize `driver_ih` to the current generated prefix variables/equations, discharge the prefix antecedent using the live branch equations plus narrow monadic rewrites, then for arbitrary `env0 st0 res0 st0'` apply the resulting theorem and take the first conjunct. Ignore/project away the extra place-expression conjunct.

#### Not to try
- Do not retry `irule driver_ih` or `match_mp_tac driver_ih` against the compact conditional premise; E0114 shows that route fails.
- Do not solve the prefix antecedent by broad whole-goal simplification with the generated IH in assumptions.
- Do not create a named adapter theorem whose statement restates the generated ExtCall prefix.
- Do not continue if the local specialization grows into a long brittle proof over multiple branches.

### C0.2.1.1.3: Nonstatic ExtCall_result branch using the same native driver-IH pattern
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: The nonstatic branch has the same success-tail driver issue plus one extra value-argument split. It should be attempted only after the static checkpoint proves the native-specialization pattern. The existing nonstatic destructor lemma supplies the extra target/amount facts, so no new proof architecture is expected.
- Dependencies: C0.2.1.1.2
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.1.3@previous, E0114
- Invalidates prior progress/evidence: C0.2.1.1.3@previous:compact-driver-premise-interface

#### Progress note
Replaces the previous 'mirror static compact helper' plan because E0114 invalidated that interface. It still carries forward the idea that nonstatic mirrors static after the proof-interface repair.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` after the static checkpoint succeeds.
- Mirror the static branch's quarantine and native driver-IH specialization.
- Use `extcall_nonstatic_args_runtime_typed_dest` to extract target address and amount.
- Keep error cases linear and closed immediately.
- Stop if the nonstatic proof requires a new adapter theorem or broad prefix cleanup.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  (* prove the nonstatic ExtCall result branch of the mutual type soundness theorem *)

#### Approach
Follow the static proof structure. After rewriting the nonstatic typing conditional, derive target address and amount with `extcall_nonstatic_args_runtime_typed_dest`; then step through the evaluator prefix one operation at a time, closing each error case immediately. At the single success continuation, use the same branch-local native specialization of captured `driver_ih` that C0.2.1.1.2 established.

#### Not to try
- Do not start before the static checkpoint.
- Do not unfold `exprs_runtime_typed_def` to recover address/amount facts; use the destructor lemma.
- Do not introduce generated-prefix adapter artifacts or broad `AllCaseEqs()` cleanup.

### C0.2.1.2: Use the opaque-driver helper to discharge the static ExtCall_result Resume
- Kind: `proof`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: Once the boundary helper exists, the static Resume branch no longer performs prefix simplification. It only reconstructs the typing/eval_exprs facts already visible in the probed goal, packages the generated prefix implication as `extcall_generated_driver_ih ... T ...`, and applies the helper.
- Dependencies: C0.2.1.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: tool_output:TO_type_system_rewrite-20260601T081233Z_m2411_t001
- Invalidates prior progress/evidence: episode:E0108 direct static linear proof attempt

#### Progress note
The static branch facts observed in the probe remain valid, but the direct prefix traversal is replaced by a helper application.

#### Summary
- Discharges only the static suspended branch.
- The proof wrapper should be short and should not traverse ExtCall monadic prefix cases.
- It packages the raw generated prefix into `extcall_generated_driver_ih ... T ...`.
- It then applies the helper from C0.2.1.1 to the existing `eval_expr` equation and context assumptions.
- Successful closure unblocks the existing downstream nonstatic/validation components.

#### Statement
Replace the `cheat` in:

```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]:
  ...
QED
```

with a proof of the existing suspended static branch goal. Do not change the theorem statement generated by `eval_all_type_sound_mutual`.

#### Approach
At the start of the static Resume, avoid any evaluator-prefix unfolding. Use the probed context facts: `eval_exprs cx es st = (INL x,args_st)`, `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, `exprs_runtime_typed env es x`, static typing facts, and the raw generated optional-driver implication. Prove a local subfact `extcall_generated_driver_ih cx es T func_name arg_types drv` by unfolding only `extcall_generated_driver_ih_def` and applying the raw generated assumption to the universally introduced prefix variables; then apply `extcall_expr_sound_from_generated_driver_ih` to the original `eval_expr` equation and existing expression-list IH/typing assumptions. If variable names differ (`is_static'`, `v15`, etc.), first perform only harmless substitutions already used by the parent Resume; do not unfold `evaluate_def` in this wrapper.

#### Not to try
Do not split `build_ext_calldata`, `get_accounts`, `run_ext_call`, or any ExtCall prefix operation in the Resume wrapper. Do not use `gvs[return_def, raise_def, no_type_error_result_def]` here. Do not discard the raw generated driver assumption before packaging it; but after packaging, keep only the opaque predicate and pass it to the helper.

### C0.2.2: Prove the nonstatic ExtCall_result suspended branch linearly
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The nonstatic branch is the same linear proof pattern as the static branch plus the explicit value extraction prefix for `HD (TL vs)`. It is standard once the static branch proof shape is established.
- Dependencies: C0.2.1
- Checkpoint: yes
- Carries progress/evidence from: E0107

#### Progress note
New leaf created by replacing the old C0.2 subtree; E0107 supports the delayed-driver-IH approach and the not-to-try constraints.

#### Summary
- Replace `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]: cheat` with a real proof.
- Follow the same linear monadic-prefix pattern as the static branch.
- Use `extcall_nonstatic_args_runtime_typed_dest` to obtain both target-address and transfer-amount extractions.
- Close failures from missing value, nonnumeric value, calldata build, account lookup/code check, run failure, and revert immediately.
- In the success path, specialize the live generated driver IH only after the full prefix and `returnData = []`/`IS_SOME drv` are available.
- Finish via `extcall_success_continuation_sound` with `value_opt = SOME amount`.

#### Description
This leaf proves only the `is_static' = F` branch. Compared to C0.2.1, it includes the extra check that `TL vs <> []` and extraction of the transfer value with `dest_NumV (HD (TL vs))`. Otherwise the proof interface and success-continuation argument are identical.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  (* real proof replacing cheat *)
QED

#### Approach
Reuse the proof shape from C0.2.1, but begin with the nonstatic argument destructor to obtain `dest_AddressV (HD vs) = SOME target_addr`, `dest_NumV (HD (TL vs)) = SOME amount`, and list nonemptiness facts. Step through the value prefix first, then `build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL vs))`, account/transient operations, `run_ext_call ... (SOME amount) ...`, success check, and state updates.

At the final success continuation, derive updated account typing, specialize the live generated-prefix driver assumption using the concrete equations in context, and apply `extcall_success_continuation_sound`. Copy only the minimal branch-local pattern from static; if the proof starts needing broad `AllCaseEqs()` cleanup, stop and report because that means the prefix has escaped the linear shape.

#### Not to try
Do not try to prove this by a combined static/nonstatic mega-proof; the value prefix makes the combined goal noisy. Do not prove a generated-prefix adapter lemma with dozens of manual `qspecl_then` arguments. Do not use the static proof by blind textual duplication if variable names/prefix states no longer match the live generated assumption; specialize the live IH only after concrete equations are present.

### C0.2.3: Validate ExtCall_result integration has no stale cheats or blocked descendants
- Kind: `integration_validation`
- Risk: 1
- Work priority: 20
- Work units: 2
- Rationale: After the two branch proofs, validation is mechanical: the local cheats should be gone and the theory should build from the restored baseline.
- Dependencies: C0.2.1, C0.2.2
- Supersedes: C0.2.2@previous
- Progress transition: `reclassified`
- Carries progress/evidence from: C0.2.2@previous, TO_type_system_rewrite-20260601T081233Z_m2390_t001

#### Progress note
The previous validation component is moved from C0.2.2 to C0.2.3 because C0.2 now has explicit static and nonstatic proof leaves before validation.

#### Summary
- Search `vyperTypeStmtSoundnessScript.sml` for the two ExtCall_result suspended-branch cheats and remove/replace any stale proof fragments.
- Build `vyperTypeStmtSoundnessTheory` after C0.2.1 and C0.2.2.
- Confirm the outer `Expr_Call_ExtCall_result` Resume still handles the argument-error branch and delegates only to the proved static/nonstatic branches.
- Confirm no forbidden broad generated-prefix adapter theorem was added for ExtCall.
- Record the build result and any remaining task-scoped cheats before moving to downstream components.

#### Description
This is an audit/build leaf, not a new proof design. It closes C0.2 only if the static and nonstatic branch proofs are real, the theory builds, and no stale suspended ExtCall_result placeholder remains.

#### Statement
Build/audit obligation: `holbuild` target `vyperTypeStmtSoundnessTheory` succeeds and the ExtCall_result static/nonstatic `cheat` placeholders are gone.

#### Approach
Use targeted grep/search in `semantics/prop/vyperTypeStmtSoundnessScript.sml` for `Expr_Call_ExtCall_result_static`, `Expr_Call_ExtCall_result_nonstatic`, and nearby `cheat` occurrences. Then run the task-approved build target. If the build fails in unrelated dirty-state code, stop and report with the exact failure rather than editing outside this C0.2 scope.

#### Not to try
Do not run broad cleanup or edit outside `semantics/prop`. Do not treat a successful build with remaining local `cheat` placeholders in the ExtCall_result branches as closure. Do not proceed to C0.3/RawCallTarget until this validation is complete.

### C0.3: Prove RawCallTarget expression-call soundness through local tail boundaries
- Kind: `proof_branch`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: E0106 isolated the problem: the Resume context is clean and the theorem is not suspected false, but the monadic RawCallTarget tail combines argument destructors, external-call side effects, flag-dependent return values, and result typing. Splitting those obligations into local helpers makes each proof analogous to already-proved neighboring helpers.
- Dependencies: C0.1
- Supersedes: C0.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0106

#### Progress note
E0106 remains useful diagnostic evidence: it proved the Resume is not polluted by ExtCall optional-driver prefix assumptions and identified the missing RawCallTarget tail boundary. The old direct-proof obligation is replaced by this helper-based decomposition.

#### Summary
- Replace the failed direct RawCallTarget proof with local boundary lemmas in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- First prove a runtime-typed argument destructor lemma for address/bytes/uint256 raw_call arguments.
- Then prove the flag-dependent returned value has `expr_result_typed` for `Call (raw_call_return_type flags) (RawCallTarget flags) es NONE`.
- Then prove one tail-result helper that owns the monadic chain, uses `run_ext_call_accounts_well_typed` and update preservation, and hides case-thrashing from the Resume.
- Finally the Resume should look like RawLog: unfold the evaluator prefix, apply expression-list IH, discharge argument typing, and invoke the tail helper.

#### Description
The failed episode showed that applying `AllCaseEqs()` and `metis_tac[raw_call_return_type_well_formed]` at the consumer leaves a huge, mixed obligation. This subtree changes the proof interface: RawCallTarget gets the same kind of local tail abstraction already used for RawLog/RawRevert/Selfdestruct, so the main mutual proof branch is only a consumer of the boundary theorem.

#### Approach
Keep all new lemmas local in `vyperTypeStmtSoundnessScript.sml`, near the existing argument/tail helpers around lines 10289-10810. Use the do-form definitions for helper proofs where possible; if the consumer produces the nested case form after prefix splitting, add a `_simp` variant matching that shape rather than redoing semantic proof in the Resume.

#### Not to try
Do not continue broad `gvs[bind_def, AllCaseEqs()]` over the entire RawCallTarget tail in the Resume. Do not `PairCases_on result` before the `lift_option (run_ext_call ...)` branch has been split to bind `result` as an actual pair. Do not encode a long generated-prefix adapter theorem; this branch has only the expression-list IH and does not need the ExtCall optional-driver workaround.

#### Argument
RawCallTarget soundness factors into three independent facts. (1) From `exprs_runtime_typed` and the well-typed raw_call argument shape, the three runtime values have the destructors required by the evaluator: address target, bytes calldata, and nonnegative uint amount. (2) External-call side effects preserve account well-typedness by `run_ext_call_accounts_well_typed`; after `update_accounts` and `update_transient`, `update_accounts_transient_runtime_consistent` reconstructs `runtime_consistent`, hence final state/env/accounts conjuncts. (3) The returned value is exactly one of the four branches of `raw_call_return_type`: `NoneV`, `BytesV (TAKE n returnData)`, `BoolV success`, or `ArrayV (TupleV [...])`; `raw_call_return_type_well_formed` plus direct evaluation/value-typing definitions prove `expr_result_typed`. The tail helper packages these facts so the mutual proof only handles evaluator prefix and expression-list IH.

#### Definition design
No evaluator or semantics definitions should change. The proof interface should consist of local theorems with conclusions matching the consumer: argument destructors, returned value typing, and a tail-result theorem whose conclusion is the full postcondition `state_well_typed ∧ env_consistent ∧ accounts_well_typed ∧ no TypeError ∧ expr_result_typed`. A failed/hard proof that repeats the whole RawCallTarget monadic prefix in the Resume is evidence that the helper statement does not match the consumer shape and should be adjusted locally.

#### Code structure
Place `raw_call_args_runtime_typed_dest` beside `send_args_runtime_typed_dest` / `raw_log_args_runtime_typed_dest`. Place `raw_call_return_value_typed` and `raw_call_tail_result_sound` / `_simp` near existing tail helpers before the RawLog/RawRevert section. Replace only the `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` body at line ~17557. Stay within `semantics/prop`.

### C0.3.1: Derive RawCallTarget runtime argument destructors
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: This is the RawCallTarget analogue of already-proved `send_args_runtime_typed_dest` and `raw_log_args_runtime_typed_dest`; it is list-shape and value-typing inversion only.
- Carries progress/evidence from: E0106

#### Progress note
Added because E0106 showed destructor facts were part of the large mixed tail goal rather than available as a boundary lemma.

#### Summary
- Prove the typed raw_call argument list yields all three evaluator destructors.
- Assumptions match the well-typed RawCallTarget branch: length 3, address at index 0, bytes at index 1, uint256 at index 2.
- This closes target/data/value TypeError branches before the external call tail.
- Use `exprs_runtime_typed_def`, `LIST_REL_EL_EQN`, `evaluate_type_def`, and `value_has_type_def` as in nearby argument helpers.

#### Statement
Theorem raw_call_args_runtime_typed_dest[local]:
  exprs_runtime_typed env es vs /\
  LENGTH es = 3 /\
  HD (MAP expr_type es) = BaseT AddressT /\
  EL 1 (MAP expr_type es) = BaseT (BytesT bd) /\
  EL 2 (MAP expr_type es) = BaseT (UintT 256) ==>
  ?target_addr calldata amount.
    dest_AddressV (HD vs) = SOME target_addr /\
    dest_BytesV (EL 1 vs) = SOME calldata /\
    dest_NumV (EL 2 vs) = SOME amount

#### Approach
Follow `raw_log_args_runtime_typed_dest`, but handle the third element like `send_args_runtime_typed_dest`. After rewriting `exprs_runtime_typed_def`, obtain `LENGTH vs = LENGTH es` and elementwise `evaluate_type` / `value_has_type` facts; case-split three-element `es`, `tvs`, and `vs` as needed. For the uint case, use the same `0 <= i` to `Num i` conversion pattern as `send_args_runtime_typed_dest`.

#### Not to try
Do not unfold the RawCallTarget evaluator here. This lemma is only about typed runtime argument values and destructors; keeping it evaluator-free is what makes it reusable in the tail helper.

### C0.3.2: Prove flag-dependent RawCallTarget return value typing
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: The proof is finite case analysis over `flags.rcf_revert_on_failure` and `flags.rcf_max_outsize = 0`, using `raw_call_return_type_well_formed` and direct value-typing definitions.
- Dependencies: C0.1
- Carries progress/evidence from: E0106

#### Progress note
Added to isolate the flag-dependent part of the 9 leftover goals from E0106.

#### Summary
- Package the four return-shape branches of raw_call into one local typing helper.
- Conclude `expr_result_typed` for `Call (raw_call_return_type flags) (RawCallTarget flags) es NONE`.
- Cover `NoneV`, dynamic bytes, `BoolV`, and tuple/array result shapes.
- Remove flag/type arithmetic from the tail and Resume proofs.

#### Statement
Prove one or more local theorems, with the main consumer-facing conclusion of this shape:

  flags.rcf_max_outsize < dimword(:256) ==>
  expr_result_typed env
    (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE)
    (Value
      (if flags.rcf_revert_on_failure then
         if flags.rcf_max_outsize = 0 then NoneV
         else BytesV (TAKE flags.rcf_max_outsize returnData)
       else if flags.rcf_max_outsize = 0 then BoolV success
       else ArrayV (TupleV [BoolV success;
                            BytesV (TAKE flags.rcf_max_outsize returnData)])))

#### Approach
Case-split `flags`, then the two tests exposed by `raw_call_return_type_def`. Rewrite `expr_result_typed_def`, `expr_runtime_typed_def`, `expr_type_def`, `toplevel_value_typed_def`, `value_has_type_def`, `evaluate_type_def`, `raw_call_return_type_def`, `materialise_def`, and `is_HashMapRef_def`; use `raw_call_return_type_well_formed` for the well-formed/evaluate-type side condition if direct rewriting leaves it. Keep this lemma independent of state and monadic bind definitions.

#### Not to try
Do not prove this inside `raw_call_tail_result_sound` by one huge `metis_tac`; E0106 showed that mixing return typing with side effects and monadic cleanup leaves unreadable goals.

### C0.3.3: Prove the RawCallTarget monadic tail result boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This is the missing proof interface identified by E0106. It can consume C0.3.1, C0.3.2, `run_ext_call_accounts_well_typed`, and `update_accounts_transient_runtime_consistent`; all TypeError sources are explicit in the tail.
- Dependencies: C0.3.1, C0.3.2
- Checkpoint: yes
- Carries progress/evidence from: E0106

#### Progress note
This is the direct repair requested by the E0106 missing-helper diagnosis.

#### Summary
- Prove a local `raw_call_tail_result_sound` or `_simp` theorem whose conclusion is the full RawCallTarget postcondition.
- The helper owns all bind/case splitting after successful `eval_exprs`.
- Close destructor/check/lift-option error cases immediately and keep one success path active.
- Use `run_ext_call_accounts_well_typed` for `accounts'` and `update_accounts_transient_runtime_consistent` after updates.
- Use C0.3.2 for the final `expr_result_typed` branch.

#### Statement
The main helper should have this consumer-facing shape (do-form or a `_simp` nested-case variant matching the Resume is acceptable):

Theorem raw_call_tail_result_sound[local]:
  !env cx es vs flags st res st' bd.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    flags.rcf_max_outsize < dimword(:256) /\
    LENGTH es = 3 /\
    HD (MAP expr_type es) = BaseT AddressT /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd) /\
    EL 2 (MAP expr_type es) = BaseT (UintT 256) /\
    ((do
        check (LENGTH vs = 3) "raw_call args";
        target_addr <- lift_option_type (dest_AddressV (HD vs)) "raw_call target";
        calldata <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
        amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
        check (~flags.rcf_is_delegate) "raw_call delegate unsupported";
        accounts <- get_accounts;
        tStorage <- get_transient_storage;
        result <- lift_option
          (run_ext_call cx.txn.target target_addr calldata
             (if flags.rcf_is_static then NONE else SOME amount)
             accounts tStorage (vyper_to_tx_params cx.txn))
          "raw_call run failed";
        (\(success,returnData,accounts',tStorage').
           do
             _ <- update_accounts (K accounts');
             _ <- update_transient (K tStorage');
             if flags.rcf_revert_on_failure then
               do
                 _ <- check success "raw_call reverted";
                 if flags.rcf_max_outsize = 0 then return (Value NoneV)
                 else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData)))
               od
             else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
             else return (Value (ArrayV (TupleV [BoolV success;
                                                  BytesV (TAKE flags.rcf_max_outsize returnData)])))
           od) result
      od) st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    case res of
    | INL tv => expr_result_typed env
                  (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE) tv
    | INR _ => T

#### Approach
First apply C0.3.1 to obtain the three successful destructor equations, then push the tail equation through `bind_def`, `ignore_bind_def`, `check_def`, `assert_def`, `raise_def`, `return_def`, `lift_option_type_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, and `update_transient_def` one operation at a time. In the success branch, split `result` only after the `lift_option (run_ext_call ...)` equation exposes it; use `run_ext_call_accounts_well_typed` to get `accounts_well_typed accounts'`, then reconstruct runtime consistency after both updates with `update_accounts_transient_runtime_consistent`. The final returned-value branch should be discharged by C0.3.2; error branches are RuntimeError or non-TypeError once destructors are known.

#### Not to try
Do not use `AllCaseEqs()` over the whole tail as the main proof method. Do not leave `result` hidden inside a nested case expression and then `PairCases_on result`; first split the `lift_option` success branch so the pair is a bound variable. If a do-form helper does not rewrite cleanly at the consumer, add a thin `_simp` theorem with the nested case statement rather than duplicating semantic reasoning in the Resume.

### C0.3.4: Replace the RawCallTarget Resume body with the boundary-helper proof
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Once C0.3.1-C0.3.3 are available, the Resume proof is the same shape as RawLog: evaluator prefix, expression-list IH, well-typed branch inversion, and one tail-helper application.
- Dependencies: C0.3.3
- Progress transition: `refinement`
- Carries progress/evidence from: E0106

#### Progress note
E0106's context probe carries forward: the Resume has the expected single expression-list IH and no ExtCall optional-driver pollution, so a boundary-helper consumer proof is appropriate.

#### Summary
- Remove the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
- Use the clean Resume context observed in E0106: one `eval_exprs` IH plus the standard expression-result/place conjunct.
- Prove the result conjunct by unfolding `well_typed_expr` and the RawCallTarget evaluator prefix, applying the IH to `eval_exprs`, and invoking the tail helper.
- Prove the place conjunct by rewriting `type_place_expr` / `well_typed_expr` as neighboring call branches do.

#### Statement
Close:

Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  ...
QED

#### Approach
Mirror the proven `Expr_Call_RawLog` Resume structure. Start with `rpt gen_tac >> strip_tac >> conj_tac`; for the expression-result conjunct, move the well-typed assumption into `mp_tac`, rewrite once with `well_typed_expr_def`, then move the evaluator equation into `mp_tac` and rewrite once with `evaluate_def`, `bind_def`, `ignore_bind_def`, `type_check_def`, `assert_def`, `return_def`, `raise_def`, `lift_option_type_def`, and `lift_option_def` only as needed to reach the `eval_exprs` split. After `eval_exprs cx es st = (INL vs,args_st)`, apply the expression-list IH, specialize the RawCallTarget typing facts, and call `raw_call_tail_result_sound` or its `_simp` variant.

#### Not to try
Do not resurrect the failed `metis_tac[raw_call_return_type_well_formed]` at the 9-goal tail. Do not perform broad cleanup over the entire monadic chain in the Resume; all tail splitting belongs in C0.3.3.

### C0.3.5: Build and audit the RawCallTarget branch locally
- Kind: `integration_validation`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: After the helper and Resume proofs, validation is mechanical: build the theory and verify this Resume no longer contains `cheat`.
- Dependencies: C0.3.4

#### Progress note
Added as a mechanical local validation after replacing the C0.3 proof strategy.

#### Summary
- Run the relevant `holbuild` target for `vyperTypeStmtSoundnessTheory`.
- Grep the RawCallTarget Resume region to ensure the `cheat` at line ~17558 is gone.
- Confirm no new edits outside `semantics/prop` were made.
- This component does not replace the later task-wide audit C0.4; it is only the local RawCallTarget closure check.

#### Approach
Use the normal build command already used in prior episodes. If the build fails in a helper proof, report the exact failing helper and goal; do not continue with large consumer-side case-thrashing.

#### Not to try
Do not treat this local audit as permission to skip C0.4, which still audits all task-scoped cheats after C0.1-C0.3.

### C0.4: Audit ExtCall_result, RawCallTarget, and builtins cheats after proof leaves
- Kind: `integration_validation`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: Once C0.1-C0.3 are complete, validation is mechanical: build the relevant theories and grep the task-scoped source for remaining real `cheat` commands. This replaces the premature old C0.5 audit with dependencies that force it to run after the proofs.
- Dependencies: C0.1, C0.2, C0.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0099
- Invalidates prior progress/evidence: C0.5@premature-audit

#### Progress note
E0099 showed the audit itself was correct but scheduled too early. This component keeps the audit idea and fixes its dependencies.

#### Summary
Run the task-scoped proof-integrity checks only after all proof leaves are done. Build `vyperTypeStmtSoundnessTheory` and the builtins target. Grep `semantics/prop/*.sml` for real remaining `cheat` commands and confirm the former locations `Expr_Call_ExtCall_result`, `Expr_Call_RawCallTarget`, and `raw_call_return_type_well_formed` are clean. Comments mentioning historical cheats are not failures unless they contain executable `cheat`.

#### Statement
Validation obligation: no executable `cheat` remains at the task-scoped locations `vyperTypeStmtSoundnessScript.sml:Expr_Call_ExtCall_result`, `vyperTypeStmtSoundnessScript.sml:Expr_Call_RawCallTarget`, or `vyperTypeBuiltinsScript.sml:raw_call_return_type_well_formed`, and the relevant HOL theories build.

#### Approach
Run the same targeted grep that found the three remaining cheats, then inspect any hits to distinguish comments from executable proof commands. Build `vyperTypeStmtSoundnessTheory`; also build the theory target affected by `vyperTypeBuiltinsScript.sml` if not already rebuilt as a dependency. If a new executable cheat appears in `semantics/prop` that is directly task-scoped, stop for strategist review rather than silently expanding scope.

#### Not to try
Do not run this audit before C0.1-C0.3 complete. Do not declare task completion merely because `holbuild` succeeds; previous evidence showed build-clean source can still contain intentional cheats. Do not edit unrelated files to silence grep hits in comments.

### C0.5: Update task-local plan/state and make the final unsigned commit
- Kind: `finalization`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: After proof and audit components, only task hygiene remains: update the task-local plan/state as requested and commit without GPG signing. This is mechanical and within the task file's explicit instructions.
- Dependencies: C0.4
- Progress transition: `replacement`
- Invalidates prior progress/evidence: C0.6@old-finalization

#### Progress note
This replaces the old final-validation component after flattening the plan.

#### Summary
Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and any task-local handoff/state file that must reflect completed progress. Ensure no edits outside `semantics/prop` are included. Run final status/audit checks. Commit the completed work with GPG signing explicitly disabled. Report completion only after the unsigned commit succeeds.

#### Statement
Final task obligation: task-local documentation is current, proof-integrity checks pass, and the final commit is made without GPG signing.

#### Approach
Review `git status` before committing and include only `semantics/prop` changes. Update the plan/state document to mention the completed ExtCall_result, RawCallTarget, and builtins helper proofs. Use an unsigned commit command such as `git -c commit.gpgsign=false commit ...`; if tooling requires signing or prompts for a password, stop and report the tooling issue.

#### Not to try
Do not commit files outside `semantics/prop`. Do not use a normal commit command if repository config may GPG-sign by default. Do not end the session as complete before the final audit and unsigned commit are both done.
