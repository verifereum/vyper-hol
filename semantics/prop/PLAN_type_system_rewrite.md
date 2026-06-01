# PLAN

## Structured Components

### C0: Type-system rewrite remaining proof obligations
- Kind: `proof_subtree_parent`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.2 risk 3. The planned consumer boundary theorem `extcall_expr_sound_from_generated_ih` does not match the actual generated IH available in the suspended Resume: the available driver fact is prefix-guarded by the full ExtCall monadic chain, not unconditional. Direct compact wiring recreates the old generated-prefix blocker.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C0 plan except C0.2.1 subtree

#### Progress note
Included only as an explicit parent required by PLAN validation. This update is scoped to C0.2.1 and does not replan C0 siblings.

#### Summary
Structural parent for the task-scoped type-system rewrite. This update only lowers the old C0.2.1 ExtCall blocker by replacing it with an executable boundary/wiring plan. All other C0 children are carried forward unchanged.

#### Argument
No new C0-level argument is introduced by this scoped update. The only changed argument is under C0.2.1: consume a proved ExtCall boundary theorem instead of simplifying the generated ExtCall prefix inside the suspended branch.

#### Definition design
No C0-level definition changes. No evaluator/semantics definitions may be changed.

#### Code structure
No C0-level file reorganization. Edits authorized by this scoped update remain in `semantics/prop` only.

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

### C0.2: ExtCall expression soundness path
- Kind: `proof_subtree_parent`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.2 risk 3. The planned consumer boundary theorem `extcall_expr_sound_from_generated_ih` does not match the actual generated IH available in the suspended Resume: the available driver fact is prefix-guarded by the full ExtCall monadic chain, not unconditional. Direct compact wiring recreates the old generated-prefix blocker.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C0.2 plan except C0.2.1 subtree

#### Progress note
Included only as an explicit dotted parent. This update does not alter C0.2 siblings such as C0.2.2/C0.2.3.

#### Summary
Structural parent for the ExtCall proof path. The only changed child is C0.2.1, which is converted from a Risk-5 report gate into a low-risk proof-boundary/wiring subtree.

#### Argument
ExtCall proof work should be done through source-local proof boundaries that isolate the evaluator's monadic prefix. C0.2.1 now uses `extcall_expr_sound_from_generated_ih` as that boundary for the result branch.

#### Definition design
No new definitions. The ExtCall interface is theorem-based: argument-error lemmas, runtime argument-shape destructors, success-continuation soundness, and the consumer theorem `extcall_expr_sound_from_generated_ih`.

#### Code structure
Keep all ExtCall helper theorem work and the relevant `Resume` edits in `semantics/prop/vyperTypeStmtSoundnessScript.sml`; update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` only for progress notes.

### C0.2.1: Unblock ExtCall result branches by direct branch-local tail-boundary application
- Kind: `proof_subtree`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.3 risk 3. The replacement plan expected direct application/projection of `extcall_success_continuation_sound_cond_driver_ih` to be a short local proof, but the actual clean success branch is already split to a single `state_well_typed st'` conjunct. Direct projection via `cj 1` does not match, and constrained metis times out. Proceeding would require either new projection helpers/goal-shape strategy or broader proof search/plumbing contrary to the stop condition.
- Supersedes: C0.2.1
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.1, E0119
- Invalidates prior progress/evidence: C0.2.1.2, E0121

#### Progress note
Carry forward the helper-stack audit and proved helper theorems. Invalidate the old proof shape that asserted a full tail postcondition in a `by` block and tried to use the generated driver IH as a direct premise.

#### Summary
- Prove static and nonstatic ExtCall result Resume branches by a linear prefix split followed by direct use of the post-update tail theorem.
- Keep generated driver IH branch-local: specialize it only after the concrete successful `run_ext_call` path and extract its expression-soundness conjunct.
- Do not introduce a long theorem reconstructing the generated ExtCall prefix.
- Remove the failed static by-subgoal attempt before retrying.

#### Argument
The ExtCall result proof has two parts. First, split the evaluator prefix linearly: argument evaluation, target extraction, calldata construction, account/code checks, external call, success check, account update, transient update. Close every error branch immediately. Second, at the post-update tail, use `extcall_success_continuation_sound_cond_driver_ih`, whose premises are exactly runtime consistency of the base state, well-typed returned accounts, return type facts, and a conditional driver IH needed only when `returnData = [] /\ IS_SOME drv`.

The generated optional-driver IH is guarded by the enclosing `Call` prefix and also contains a place-expression conjunct. In the single concrete success branch, derive a local expression-only driver fact by specializing the saved generated IH, discharging its prefix guard with the equations already produced by the linear split, and projecting the expression-soundness conjunct. This local fact is the premise passed to the continuation theorem.

#### Definition design
No definitions change. Boundary interfaces are:
- `run_ext_call_accounts_well_typed`: proves `accounts_well_typed accounts'` from a successful `run_ext_call`.
- `update_accounts_transient_runtime_consistent`: used inside the tail theorem, not by Resume consumers.
- `extcall_success_continuation_sound_cond_driver_ih`: branch-facing post-update tail theorem, intentionally conditional in the driver premise.
Failure signs: broad `AllCaseEqs()` over the full prefix, a generated-prefix adapter theorem, or manual theorem plumbing with copied full assumptions. If driver-IH extraction is not a short local proof in the concrete success branch, stop and escalate.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep helper theorems near the existing ExtCall helper block. The two Resume branches should contain only the linear prefix split, a small branch-local driver-IH extraction, and direct continuation-theorem application.

### C0.2.1.1: Carry forward ExtCall helper-stack audit
- Kind: `proof_boundary_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: The audit/proved helper stack remains valid; E0121 only invalidates the Resume-facing placement of the boundary.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.1, E0119

#### Progress note
No new work; preserves accepted helper-audit progress.

#### Summary
- Keep the proved ExtCall helper stack.
- `run_ext_call_accounts_well_typed` and `extcall_success_continuation_sound_cond_driver_ih` remain intended interfaces.
- No source changes required.

### C0.2.1.2: Remove the failed static by-subgoal attempt before retrying
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: The dirty proof shape from E0121 is misleading and should not be repaired in place.
- Dependencies: C0.2.1.1
- Supersedes: C0.2.1.2
- Progress transition: `replacement`
- Invalidates prior progress/evidence: E0121

#### Progress note
Replaces old C0.2.1.2 with cleanup; E0121 counts only as negative evidence.

#### Summary
- In the static Resume, remove the failed local assertion of the full post-update tail postcondition if present.
- Restore the success branch to a clean linear prefix-split state with one precise tail goal or one explicit cheat at that point.
- Ensure no `ACCEPT_TAC driver_ih` remains for the conditional premise and no obsolete `by` wrapper remains.

#### Approach
Keep clean prefix splits and the `accounts_well_typed` derivation if present. Remove only the failed proof block that tried to prove the whole tail postcondition in backquotes; C0.2.1.3 will apply the continuation theorem directly to the actual goal.

#### Not to try
Do not patch the old `by` assertion with more `simp`, `gvs`, or generated prefix equations.

### C0.2.1.3: Close static ExtCall success tail before postcondition splitting
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The continuation theorem is usable against the full ExtCall tail postcondition, not against an already-projected `state_well_typed st'` subgoal. The local repair is to delay the simplifier/conjunction split in the `success = T` case and apply the full tail theorem first.
- Checkpoint: yes
- Supersedes: C0.2.1.3
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.3.1, E0125, E0127
- Invalidates prior progress/evidence: C0.2.1.3.2@previous

#### Progress note
Carries forward proved helper work from E0125 and uses E0127 as evidence invalidating the projected-use plan.

#### Summary
- Repair only the static ExtCall success-tail branch in `vyperTypeStmtSoundnessScript.sml`.
- Do not try to project the already-split goal `state_well_typed st'`.
- Keep the proved projection lemmas as optional infrastructure, but do not depend on them for this use site.
- In the `success = T` branch, preserve the full postcondition goal until `extcall_success_continuation_sound_cond_driver_ih` can be applied.
- Continue closing error branches immediately and avoid broad generated-prefix recovery.

#### Description
E0127 showed that after `Cases_on x'0 >> gvs[...]`, HOL has split the final theorem postcondition and the active goal is only `state_well_typed st'`. At that point neither the state projection theorem nor the saved generated IH matches directly, and broad simplification of the generated IH violates the maintainer stop condition. The proof must be reordered so the success tail is handled before that projection occurs.

#### Approach
Refactor the static Resume around the success split. In the success case, avoid the immediate `gvs[return_def, raise_def]` pattern that decomposes the final conjunction; keep or assert the full postcondition and apply `extcall_success_continuation_sound_cond_driver_ih`. Instantiate it with the branch-local `args_st`, returned accounts, returned transient storage, and return data exposed by `PairCases_on x'`.

#### Not to try
Do not use `irule extcall_success_continuation_state_well_typed` on a lone `state_well_typed st'` goal. Do not use `mp_tac driver_ih >> simp[]`, broad `gvs`, `AllCaseEqs()`, or a long generated-prefix adapter theorem.

#### Argument
The ExtCall success tail after `run_ext_call` has the exact monadic structure captured by `extcall_success_continuation_sound_cond_driver_ih`: assert success, update accounts, update transient storage, then evaluate the optional driver or decode return data. That theorem proves the whole combined postcondition, so it should be applied before the final goal is split into separate state/env/accounts/result projections.

#### Definition design
No definition changes. The boundary is the post-update continuation computation. Failure sign: the active goal is a single projection such as `state_well_typed st'` and the continuation theorem no longer matches directly.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. The helper theorem block is around the existing ExtCall continuation lemmas; the Resume repair is near `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`.

### C0.2.1.3.1: Retain ExtCall continuation projection lemmas as optional infrastructure
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0125 proved these lemmas. E0127 only showed they are not the right primary interface for this use site.
- Supersedes: C0.2.1.3.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.1, E0125

#### Progress note
The lemmas remain valid but are demoted to optional infrastructure.

#### Summary
- Keep the proved local projection lemmas from E0125.
- Treat them as optional infrastructure, not the required path for the static success-tail branch.
- No source work is required for this child.
- Do not force the proof into a projected-goal shape to use them.

#### Approach
No action unless a rebuild shows the lemmas were accidentally removed.

#### Not to try
Do not adapt the static success-tail branch to these projections; that was the failed strategy.

### C0.2.1.3.2: Refactor the static success branch to apply the full continuation theorem
- Kind: `proof`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: This is a local proof-ordering change with a known theorem matching the full branch postcondition. The prior failure gives a clear negative boundary: do not simplify into projected subgoals before applying the theorem.
- Dependencies: C0.2.1.3.1
- Checkpoint: yes
- Supersedes: C0.2.1.3.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0127
- Invalidates prior progress/evidence: C0.2.1.3.2@previous-use-site-projection

#### Progress note
Replaces the failed projected-use plan with a full-postcondition-before-splitting plan.

#### Summary
- Edit only `Expr_Call_ExtCall_result_static`.
- After `run_ext_call` succeeds and `PairCases_on x'` exposes the result tuple, split on success without simplifying the final postcondition into separate conjunct goals.
- In the success branch, apply `extcall_success_continuation_sound_cond_driver_ih` to the full goal.
- Supply branch-local runtime consistency, functions, accounts typing from `run_ext_call_accounts_well_typed`, optional-driver typing, return type well-formedness, driver return type, and the conditional driver IH.
- Rebuild `vyperTypeStmtSoundnessTheory`; the nonstatic ExtCall cheat remains separate.

#### Description
The direct projection attempt failed because simplification after the success split moved the proof into the first conjunct of the final postcondition. Restructure the local case split so the success branch goal remains the full combined postcondition, then use the full continuation theorem.

#### Statement
Replace the explicit `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` success branch with a proof of the combined postcondition using `extcall_success_continuation_sound_cond_driver_ih` before the conjunction is split.

#### Approach
Use a local assertion/suffices step if helpful: assert the full postcondition for the success-tail computation by `irule extcall_success_continuation_sound_cond_driver_ih`, then use that assertion to close the current goal. For the conditional driver premise, only after the branch is isolated assume `returnData = [] /\ IS_SOME drv`, destruct `drv`, and use the saved generated `driver_ih` with the concrete post-update state; do not simplify the earlier ExtCall prefix.

#### Not to try
Do not apply `extcall_success_continuation_state_well_typed` to the split `state_well_typed st'` goal. Do not try direct `ACCEPT_TAC driver_ih`/`MATCH_ACCEPT_TAC driver_ih`. Do not run broad `simp`/`gvs` on `driver_ih` or the full generated prefix.

### C0.2.1.3.3: Audit static ExtCall branch build and remaining cheats
- Kind: `proof_audit`
- Risk: 1
- Work priority: 2
- Work units: 1
- Rationale: After the refactor, validation is mechanical: the target theory should build, the static success-tail cheat should be gone, and the nonstatic ExtCall cheat may remain for its own later component.
- Dependencies: C0.2.1.3.2
- Checkpoint: yes

#### Progress note
New audit leaf added after a checkpoint repair.

#### Summary
- Run/confirm `holbuild` for `vyperTypeStmtSoundnessTheory`.
- Confirm the static success-tail cheat is removed.
- Confirm no failed probe/diff remains and no files outside `semantics/prop` were edited.
- Confirm the nonstatic ExtCall Resume remains a separate obligation.

#### Approach
Use grep/build evidence. If the repaired static branch fails with a new interface mismatch, stop and escalate rather than broadening simplification.

#### Not to try
Do not proceed into the nonstatic branch under this audit component. Do not mask failure by leaving or moving a cheat.

### C0.2.1.4: Close the nonstatic ExtCall success tail using the validated direct pattern
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Nonstatic is analogous after its extra value-argument prefix split; it must reuse the static direct-tail pattern.
- Dependencies: C0.2.1.3
- Checkpoint: yes
- Supersedes: C0.2.1.3
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.3

#### Progress note
Replaces the old nonstatic plan only to require the validated direct application pattern.

#### Summary
- Work in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]`.
- Split the extra nonstatic value checks linearly.
- Use `run_ext_call_accounts_well_typed` and apply `extcall_success_continuation_sound_cond_driver_ih` directly to the current goal.
- Extract the conditional driver premise branch-locally only on `returnData = [] /\ IS_SOME drv`.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic] closes without cheat using the same direct branch-local tail-boundary pattern.

#### Approach
Mirror static after the nonstatic-specific prefix has produced `run_ext_call ... (SOME amount)`. Error branches close immediately. The success tail should be textually close to C0.2.1.3, differing only in the nonstatic prefix equations.

#### Not to try
Do not start until the static checkpoint is accepted. Do not copy the failed static `by` assertion or invent a generated-prefix adapter.

### C0.2.1.5: Remove obsolete ExtCall compact-boundary artifacts after both branches build
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: Stale artifacts suggesting the invalid compact/generated-prefix approach should be removed after both branches build.
- Dependencies: C0.2.1.4
- Supersedes: C0.2.1.4
- Progress transition: `replacement`

#### Progress note
Retains the old cleanup intent but schedules it after the new branch proofs.

#### Summary
- Remove or quarantine unused ExtCall artifacts encoding the invalidated compact strategy.
- Keep successful local tail theorems and branch proofs.
- Build after cleanup.

#### Approach
Search only within `semantics/prop`. Delete misleading unused helper statements/comments after both static and nonstatic branches build.

#### Not to try
Do not clean up before branch proofs are stable.

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
