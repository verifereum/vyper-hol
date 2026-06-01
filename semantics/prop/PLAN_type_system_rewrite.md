# PLAN

## Structured Components

### C0: Type-system rewrite proof completion
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: This local merge only repairs the ExtCall_result subtree; no new whole-task obstruction is introduced by E0111 once the generated IH is quarantined rather than kept as a simplification assumption.
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
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The ExtCall_result branch remains plausible after E0111 if the generated optional-driver implication is treated as an opaque theorem object and removed from assumptions during prefix splitting.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2

#### Progress note
Parent included only for local subtree context; sibling obligations are not rewritten by this review.

#### Summary
ExtCall proof subtree. The key repair is local theorem quarantine, not evaluator-definition changes or generated-prefix adapter resurrection.

### C0.2.1: Quarantine generated ExtCall driver IH and prove ExtCall_result branches
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: E0111 showed the previous direct proof was not Risk 2 while the raw generated prefix implication was live. The revised proof interface removes that implication from the assumptions before simplification and reuses it only at the single success tail, matching the maintainer-approved specialization point.
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

### C0.2.1.1: Prove ExtCall expression result soundness with quarantined optional-driver IH
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: E0111 invalidated the previous Risk-2 claim for leaving the generated optional-driver implication live. The revised subtree is Risk 2 because it makes quarantine a required proof interface: the raw generated implication is removed before any `simp`/`gvs`, preventing prefix-error cleanup from traversing the >4KiB generated premise. The only non-mechanical step is reapplying the captured theorem in the final success tail by matching its conclusion, exactly the maintainer-approved specialization point.
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.1.1, E0110, E0111
- Invalidates prior progress/evidence: C0.2.1.1.2@previous

#### Progress note
Carries forward the successful cleanup of obsolete generated-prefix artifacts from E0110 and the negative evidence from E0111. Invalidates only the earlier direct-linear approach that kept the raw driver implication live during prefix splitting.

#### Summary
- Local replacement for the ExtCall_result proof branch after E0111.
- The raw generated optional-driver implication is proof data, not a simplification assumption.
- Capture/remove it at the start of each ExtCall branch with `qpat_x_assum ... (fn driver_ih => ...)`.
- Do all prefix-error and static/nonstatic splitting while that theorem is absent from assumptions.
- Reintroduce it only in the final concrete success-continuation branch to discharge the conditional driver premise of `extcall_success_continuation_sound_cond_driver_ih`.

#### Description
E0111 showed that even narrow simplification and local case splitting time out when the raw generated optional-driver implication remains among assumptions. The revised invariant is therefore syntactic as much as mathematical: before simplification of the ExtCall evaluator prefix, consume the generated implication by `qpat_x_assum` into an ML theorem value and thereby remove it from the goal. Prefix work then uses existing small boundary lemmas without broad assumption simplification.

#### Approach
In each `Expr_Call_ExtCall_result_static`/nonstatic branch, immediately capture the generated optional-driver IH assumption using a precise `qpat_x_assum` pattern whose body is the long `∀s'' vs ... . ... ⇒ ∀env st res st'. ...` implication. The continuation tactic should run all evaluator-prefix splitting with that theorem bound as `driver_ih` and no longer present as an assumption. At the success tail, invoke `extcall_success_continuation_sound_cond_driver_ih`; for its conditional driver premise, `strip_tac` the `returnData = [] /\ IS_SOME drv` antecedent, then use `irule driver_ih` or `match_mp_tac driver_ih` so HOL instantiates the generated prefix from the concrete prefix equalities already in context, followed only by narrow rewriting of those prefix equalities.

#### Not to try
Do not leave the raw generated optional-driver implication in the assumption set while calling `simp[]`, `gvs[]`, `Cases_on vs`, or unfolding `evaluate_def`; E0111 shows this causes timeouts and huge goals. Do not resurrect `extcall_generated_driver_ih`, build long generated-prefix adapter theorems, or use broad `AllCaseEqs()`/assumption cleanup over the whole ExtCall prefix. Do not manually `qspecl_then` the generated IH with the entire prefix-state variable list; if matching cannot instantiate it from the concrete success branch, stop and escalate.

#### Argument
The ExtCall result proof has two phases. First, the evaluator prefix establishes either an immediate error result or a single successful external-call continuation with concrete `accounts'`, `tStorage'`, `returnData`, and updated state. This phase does not need the optional-driver IH and should not expose it to simplification. Second, only in the success continuation, the return-data/driver tail is exactly the computation covered by `extcall_success_continuation_sound_cond_driver_ih`; if `returnData = []` and `drv` is present, the captured generated IH supplies soundness of `eval_expr cx (THE drv)` after the preceding prefix equations have all been established. Thus prefix facts are produced linearly and the generated IH is consumed once at its natural boundary.

#### Definition design
No evaluator or semantics definitions may change. The proof interface is local theorem management: the generated optional-driver IH is treated like an opaque theorem object. Boundary lemmas should have compact conclusions matching use sites: static args give `dest_AddressV (HD vs) = SOME target_addr` and `vs <> []`; the tail helper consumes a compact conditional optional-driver premise plus updated accounts/transient state. Failure sign: any prefix proof goal whose assumptions still contain the raw `∀s'' vs ... update_transient ... returnData = [] /\ IS_SOME drv ⇒ ...` implication means quarantine was missed and the proof should stop.

#### Code structure
All work remains in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep the existing local helper block near `extcall_success_continuation_sound_cond_driver_ih` and the static/nonstatic argument destructor lemmas. The Resume bodies at `Expr_Call_ExtCall_result_static` and then `Expr_Call_ExtCall_result_nonstatic` should implement the quarantine pattern directly; add only tiny local helper lemmas for repeated argument destructuring, not generated-prefix adapters.

### C0.2.1.1.1: Remove obsolete generated-prefix ExtCall driver artifacts
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed and build-checked in E0110; keep as carried-forward cleanup because the replacement subtree still depends on not reviving the obsolete generated-prefix adapter path.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0110, C0.2.1.1.1

#### Progress note
E0110 proved this cleanup; no further executor work is required.

#### Summary
- Completed cleanup leaf retained for continuity.
- Obsolete generated-prefix artifacts remain deleted.
- This prevents accidental return to the forbidden E0109 adapter-theorem approach.

#### Description
No direct work remains. The build-clean baseline after E0111 confirms exploratory edits were reverted and the cleanup remains valid.

#### Approach
No action unless a later build shows the cleanup was accidentally reverted. If so, restore the E0110 state and build-check.

#### Not to try
Do not reintroduce the deleted generated-prefix theorem family as a workaround for the static/nonstatic branch proof.

### C0.2.1.1.2: Static ExtCall_result branch with generated-driver IH quarantined
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: The static branch is Risk 2 only under the explicit quarantine pattern. The previously observed timeouts are avoided because the raw generated implication is removed before simplification and case splitting. The success-tail use is localized to the exact branch where all prefix equalities are present.
- Dependencies: C0.2.1.1.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0111
- Invalidates prior progress/evidence: C0.2.1.1.2@previous

#### Progress note
E0111 remains supporting evidence for why the old live-assumption approach is invalid. This component replaces it with a stricter proof interface rather than retrying the same simplification sequence.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`.
- First action inside the proof must capture/remove the raw generated optional-driver implication.
- Simplify the static typing conditional with `rewrite_tac[boolTheory.COND_CLAUSES]`, not `simp[]` over all assumptions.
- Use existing static argument destructor/nonempty lemmas; avoid local `Cases_on vs` with `gvs[]` while large assumptions are live.
- Split the evaluator prefix linearly and close error cases immediately.
- At the single success tail, apply `extcall_success_continuation_sound_cond_driver_ih` and discharge its conditional driver premise using the captured `driver_ih` by matching, not manual prefix instantiation.

#### Description
This is the direct repair for the failed episode. The proof must demonstrate that the quarantine tactic prevents the timeouts seen in E0111. Because this is a checkpoint, stop after the static branch builds and report whether the captured theorem can be reapplied at the success tail without a long generated-prefix adapter.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]:
  (* prove the static ExtCall result branch of the mutual type soundness theorem *)

#### Approach
Begin with `rpt gen_tac >> strip_tac`, then immediately use `qpat_x_assum` to remove the long generated optional-driver implication into a theorem variable, e.g. `fn driver_ih => ...`. Inside that continuation, rewrite the static typing conditional using `rewrite_tac[boolTheory.COND_CLAUSES] >> strip_tac`, derive address/nonempty facts via `extcall_static_args_runtime_typed_dest` and `extcall_static_args_runtime_typed_nonempty`, and unfold only the current evaluator/monadic prefix. For the final tail, `irule extcall_success_continuation_sound_cond_driver_ih`; the driver-premise subgoal should be solved by `strip_tac >> irule driver_ih` (or `match_mp_tac driver_ih`) followed by narrow rewriting from the concrete prefix equations in context.

#### Not to try
Do not call `simp[]` or `gvs[]` while the generated optional-driver implication is still an assumption; this is exactly what timed out in E0111. Do not prove `vs <> []` by `Cases_on vs >> gvs[exprs_runtime_typed_def]`; use `extcall_static_args_runtime_typed_nonempty`. Do not manually instantiate the generated IH with every `s'³'`, `t'⁴'`, etc.; matching from the concrete success branch is the required low-risk interface. If matching cannot discharge the generated prefix antecedent after all success-prefix facts are assumptions, escalate rather than building an adapter theorem.

### C0.2.1.1.3: Nonstatic ExtCall_result branch with the same quarantine interface
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: The nonstatic branch should mirror the static proof once C0.2.1.1.2 proves the quarantine pattern works. It has one extra value-argument split, but the same proof boundary and success-tail helper apply.
- Dependencies: C0.2.1.1.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.1.1.3

#### Progress note
Refines the old not-started success-tail component into the nonstatic branch proof using the same validated quarantine interface.

#### Summary
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` after the static checkpoint.
- Reuse the same generated-IH quarantine pattern as the static branch.
- Split the additional nonstatic value argument prefix linearly and close error cases immediately.
- Reuse the existing tail helper at the success continuation.
- Escalate if the nonstatic argument destructor interface is missing a compact helper analogous to the static destructor lemmas.

#### Description
This component should not start until the static branch confirms the proof interface. The expected difference from static is the extra `dest_NumV`/value argument handling before `build_ext_calldata`; if existing helper lemmas do not provide a compact destructor/nonempty fact, request a small boundary lemma rather than unfolding `exprs_runtime_typed_def` under large goals.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  (* prove the nonstatic ExtCall result branch of the mutual type soundness theorem *)

#### Approach
Copy the static branch structure: capture/remove the generated optional-driver implication first; rewrite the nonstatic typing conditional narrowly; derive target address and value-argument facts through compact helper lemmas; unfold and split one monadic operation at a time. Use `extcall_success_continuation_sound_cond_driver_ih` at the final success tail and discharge the conditional driver premise with the captured theorem by matching.

#### Not to try
Do not generalize the nonstatic branch into a shared generated-prefix adapter. Do not use broad `AllCaseEqs()` or whole-prefix `gvs[]`. If a needed nonstatic argument destructor is absent, add/request a tiny boundary lemma instead of destructing the whole `exprs_runtime_typed` relation in the Resume body.

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
