# PLAN

## Structured Components

### C0: Complete the task-scoped type-system rewrite obligations in semantics/prop
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.3 risk 3. The direct neighboring-branch proof leaves a >4KiB RawCallTarget tail obligation involving `run_ext_call`, account/transient updates, revert flags, max_outsize-dependent return values, and result typing. This needs a RawCallTarget tail boundary lemma (analogous to existing raw_log/raw_revert/selfdestruct tail helpers) or a repaired decomposition; the current plan's claim that the branch is straightforward by direct unfolding is under-specified.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, E0103, E0105

#### Progress note
Top-level strategy is unchanged; only the C0.2 ExtCall_result branch decomposition/schedule is repaired.

#### Summary
- Task remains scoped to the type-system rewrite proof work in `semantics/prop`.
- E0105 is accepted as diagnostic evidence for an ExtCall_result proof-interface hazard.
- The repaired C0.2 subtree keeps generated optional-driver IHs opaque until concrete success continuations.
- No evaluator/semantics definitions or files outside `semantics/prop` are to be edited.

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

### C0.2: Close ExtCall_result by linear branch proofs using the generated driver IH in-place
- Kind: `proof_refactor_subtree`
- Risk: 3
- Work priority: 20
- Work units: 0
- Rationale: Derived from child component C0.2.1 risk 3. The replacement C0.2.1 plan rated the static suspended branch Risk 2 and straightforward by linear prefix unfolding, but even the first static-branch prefix split leaves multiple active goals with the huge generated optional-driver IH and causes simplification/cleanup timeouts. Proceeding would require design/proof-interface work contrary to the user's stop condition.
- Supersedes: C0.2, C0.2.1
- Progress transition: `replacement`
- Carries progress/evidence from: E0107, TO_type_system_rewrite-20260601T081233Z_m2388_t001, TO_type_system_rewrite-20260601T081233Z_m2390_t001
- Invalidates prior progress/evidence: C0.2@previous, C0.2.1@previous

#### Progress note
E0107 is accepted as valid evidence that the previous C0.2/C0.2.1 interface was wrong-shaped. The build-clean placeholder baseline still carries forward, but the direct-boundary theorem plan no longer counts as proof progress.

#### Summary
- Replace the failed direct-boundary theorem application with branch-local linear proofs for `Expr_Call_ExtCall_result_static` and `_nonstatic`.
- Use the existing `Expr_Call_ExtCall_result` skeleton: arguments are already evaluated, typed, and split into static/nonstatic suspended branches.
- In each branch, unfold only the current ExtCall evaluator prefix one operation at a time, closing each error case as it appears.
- Only after reaching the unique success continuation with `returnData = []` and `IS_SOME drv`, specialize the generated optional-driver IH from the live context.
- Do not manufacture an unconditional driver IH or recover it by global simplification over the generated prefix.
- Final validation is a build/search audit that the ExtCall_result branches have no remaining cheats or stale suspended leaves.

#### Description
E0107 showed that `extcall_expr_sound_from_generated_ih` has the wrong interface for the generated mutual proof. The available optional-driver IH is not a standalone assumption; it is an implication guarded by the concrete ExtCall success chain. This subtree therefore proves the static and nonstatic suspended branches directly at the point where the necessary prefix facts are live, delaying driver-IH specialization until all guards are discharged by the branch proof itself.

#### Approach
Keep the already-good outer `Expr_Call_ExtCall_result` skeleton: it uses the expression-list IH, handles `INR` argument errors through `eval_extcall_args_error_any_call_ty_result_eq`, and suspends only after `args_res = INL vs`, `exprs_runtime_typed env es vs`, `v15 = ret_type`, and the static/nonstatic split. Fill each suspended branch by local evaluator-prefix reasoning, not by applying `extcall_expr_sound_from_generated_ih`. At the success continuation, use the live generated-prefix assumption directly to obtain the expression soundness of `THE drv`; then feed that to `extcall_success_continuation_sound`.

#### Not to try
Do not use `MATCH_MP_TAC (Q.SPECL [...] extcall_expr_sound_from_generated_ih)` in `Expr_Call_ExtCall_result`; E0107 proves its unconditional driver-IH premise is not available. Do not add a long generated-prefix adapter theorem just to convert the live implication into an unconditional IH. Do not use broad `simp`/`gvs`/`fs` with `AllCaseEqs()` over the whole ExtCall prefix from the top-level Resume context.

#### Argument
The outer ExtCall proof is by the existing generated mutual induction for expressions. The argument-evaluation prefix is already handled uniformly: if `eval_exprs` returns `INR`, the existing error lemma transfers the well-typed state and no-type-error result to the whole call. If `eval_exprs` returns `INL vs`, the expression-list IH gives `exprs_runtime_typed env es vs`; the well-typed-call equation fixes `call_ty = ret_type` and gives `well_typed_opt env drv`, `well_formed_type env.type_defs ret_type`, and the static/nonstatic argument-shape facts.

For each branch, runtime typing destructors (`extcall_static_args_runtime_typed_dest` and `extcall_nonstatic_args_runtime_typed_dest`) justify the address/value extractions. The evaluator prefix then consists only of monadic checks/lifts/state operations/run_ext_call. Every failing check/lift/run case returns a runtime error or preserves the already well-typed intermediate state, so those cases close immediately by `no_type_error_result_def`, state/account preservation facts, or the corresponding prefix equation.

In the single success path, `run_ext_call_accounts_well_typed` supplies well-typed updated accounts. The branch proof has concrete equations for the whole generated prefix, including `returnData = []` and `IS_SOME drv`; only there is the generated optional-driver IH specialized to `THE drv`. The final result follows by `extcall_success_continuation_sound`, with `runtime_consistent_def`, `functions_well_typed`, `well_formed_type`, `well_typed_opt`, the updated accounts, and the specialized driver soundness premise.

#### Definition design
No evaluator/type-system definitions should change. The proof interface is the live generated optional-driver IH itself: a guarded implication whose guards are exactly the ExtCall prefix equations plus `returnData = []` and `IS_SOME drv`. Treat this as a branch-local resource, not as an unconditional theorem. A failure sign is any proof attempt that tries to prove `!env st res st'. ... eval_expr cx (THE drv) st = ... ==> ...` before the branch has discharged the ExtCall success-prefix guards. Acceptable consumers are small existing boundary lemmas such as `extcall_success_continuation_sound`, `run_ext_call_accounts_well_typed`, and the static/nonstatic runtime-typed destructors.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Do not edit evaluator or semantic definition files. Keep the current `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` outer skeleton and replace only the `cheat` bodies of `Expr_Call_ExtCall_result_static` and `Expr_Call_ExtCall_result_nonstatic`. If tiny local proof helpers are unavoidable, place them near the existing ExtCall helper block and keep them branch-consumer shaped; do not introduce a broad generated-prefix adapter theorem. The final child performs the build/search audit in `semantics/prop` only.

### C0.2.1: Quarantine the generated ExtCall driver IH and prove the static ExtCall_result branch
- Kind: `proof_refactor`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.1.1 risk 3. The redesigned opaque-driver helper is not a straightforward Risk-2 boundary lemma: proving the success-tail driver premise still requires opening/specializing the generated prefix with long brittle state-variable plumbing and produces a >4KiB goal. This is the same proof-interface hazard E0108 was meant to avoid, now moved into the helper.
- Supersedes: C0.2.1
- Progress transition: `replacement`
- Carries progress/evidence from: episode:E0108, tool_output:TO_type_system_rewrite-20260601T081233Z_m2411_t001, tool_output:TO_type_system_rewrite-20260601T081233Z_m2421_t001
- Invalidates prior progress/evidence: C0.2.1 previous direct linear static-branch proof plan

#### Progress note
Carries forward E0108 only as negative design evidence. The previous direct linear static branch proof progress is invalidated because its interface exposed the generated prefix in prefix-error branches; this replacement changes the proof boundary rather than asking for more tactics on the same goal.

#### Summary
- Replace the failed direct static Resume proof with an opaque-driver boundary helper plus a tiny static Resume wrapper.
- The helper proves the ExtCall expression postcondition from `extcall_generated_driver_ih`, not from an unconditional driver IH and not from the raw expanded generated prefix.
- Prefix-error cases are handled inside the helper with the driver predicate kept opaque; the predicate is opened only at the final success continuation.
- The static Resume branch then builds `extcall_generated_driver_ih cx es T func_name arg_types drv` from the generated Resume assumption and applies the helper.
- This supersedes the E0108 static linear-prefix attempt; downstream nonstatic/validation work stays gated until this static branch is proved.

#### Description
The existing theorem `extcall_expr_sound_from_generated_ih` is the wrong interface for the generated mutual proof: it asks for an unconditional optional-driver IH, while the Resume context supplies a guarded prefix implication. The static branch also must not simplify while that raw guarded implication is live. The replacement interface is a local helper, e.g. `extcall_expr_sound_from_generated_driver_ih`, with the same conclusion as `extcall_expr_sound_from_generated_ih` but with `extcall_generated_driver_ih cx es is_static func_name arg_types drv` as the driver premise. The helper treats this predicate as opaque until the concrete ExtCall success continuation and then uses the existing eliminator `extcall_generated_driver_ih_elim_expr`.

#### Approach
First prove the new local helper near the existing ExtCall helper block, by cloning the successful structure of `extcall_expr_sound_from_generated_ih` but replacing the unconditional driver premise with the opaque `extcall_generated_driver_ih` assumption. Then prove `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` by reconstructing only the small already-known typing/eval_exprs context, proving/assuming `extcall_generated_driver_ih cx es T func_name arg_types drv` from the raw generated Resume premise with `rw[extcall_generated_driver_ih_def]`/direct assumption application, and applying the helper. Do not attempt to finish the nonstatic branch in this component.

#### Not to try
Do not retry broad or targeted `simp`/`gvs`/`AllCaseEqs()` over the static evaluator prefix while the raw generated optional-driver implication is in the assumptions; E0108 timed out there. Do not use `extcall_expr_sound_from_generated_ih` directly: its unconditional optional-driver IH premise is stronger than what the generated Resume context provides. Do not introduce a new long adapter theorem whose only purpose is to recover that unconditional premise; the point is to keep the generated prefix behind the existing opaque predicate and open it only at the success tail.

#### Argument
The ExtCall evaluator has two conceptually independent parts: (1) argument evaluation and a deterministic monadic prefix through target extraction, optional value extraction, calldata construction, accounts/transient lookup, external call, success check, and state updates; (2) an optional driver expression that is evaluated only after the entire prefix succeeds and returns empty data. Soundness of prefix error cases does not depend on the driver IH at all: those branches either preserve the current runtime-consistent state or return a non-TypeError runtime error from `check`, `lift_option`, or `run_ext_call` failure. Soundness of the final continuation does depend on the driver IH, but only under the exact prefix-success facts already produced by the evaluator. Therefore the correct proof interface is a helper that keeps the generated driver premise opaque during prefix traversal and specializes it only in the concrete success branch. This avoids both the false/unavailable unconditional-driver premise and the simplifier blow-up from carrying the expanded generated prefix through unrelated branches.

#### Definition design
Use the already-present abstraction `extcall_generated_driver_ih_def` as the boundary predicate. Its proof interface is intentionally opaque: consumers should assume `extcall_generated_driver_ih cx es is_static func_name arg_types drv` and must not unfold it except in a tiny packaging proof or at the final success continuation through `extcall_generated_driver_ih_elim_expr`. The helper boundary lemma should have a statement matching the existing call-soundness helper conclusion, so the Resume wrapper can use `MATCH_MP_TAC`/`irule` with direct assumptions. A failure sign is any goal where the expanded prefix implication appears while proving build-calldata/account/code/run/revert error cases; if that happens, the boundary has been unfolded too early and the component should stop rather than optimize tactics.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Put the new local helper near `extcall_expr_sound_from_generated_ih` and `extcall_generated_driver_ih_def`, before the suspended `Resume` blocks. Reuse existing local lemmas such as `extcall_static_args_runtime_typed_dest`, `extcall_success_continuation_sound`, `run_ext_call_accounts_well_typed`, and `extcall_generated_driver_ih_elim_expr`; do not edit evaluator/semantics definitions or files outside `semantics/prop`. The static Resume proof at line ~17500 should become a short wrapper around the new helper; leave the nonstatic cheat for its own existing component.

### C0.2.1.1: Prove ExtCall expression result soundness by direct linear branch proof
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The high-risk generated-prefix adapter is abandoned. The remaining proof shape is low-risk because existing local helpers already cover the semantic tail (`extcall_success_continuation_sound_cond_driver_ih`), ABI return typing, state updates, argument runtime destructors, and account preservation. The only delicate step is to specialize the generated optional-driver IH after reaching the concrete success tail; the maintainer explicitly authorized that narrow shape.
- Supersedes: C0.2.1.1@E0109
- Progress transition: `replacement`
- Carries progress/evidence from: E0109, TO_type_system_rewrite-20260601T081233Z_m2455_t001, TO_type_system_rewrite-20260601T081233Z_m2458_t001, TO_type_system_rewrite-20260601T081233Z_m2460_t001
- Invalidates prior progress/evidence: old C0.2.1.1 opaque-driver helper plan

#### Progress note
E0109 remains valid evidence that the opaque-driver/generated-prefix helper interface is unacceptable. This replacement carries forward the diagnosis and reuses the successful localization from TO_m2455, but invalidates the old helper as a proof target.

#### Summary
- Replace the failed opaque-driver boundary plan with a direct proof of `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`.
- Do not introduce or consume `extcall_generated_driver_ih`; E0109 proved that interface is too close to the generated prefix.
- The proof should unfold the ExtCall evaluator linearly, closing each error branch immediately.
- Only after the concrete successful `run_ext_call`/state-update tail is reached should the generated optional-driver IH be specialized.
- Existing tail helper `extcall_success_continuation_sound_cond_driver_ih` is the proof boundary: it needs only a compact conditional driver premise, not the entire generated prefix.

#### Approach
Work inside the existing suspended theorem `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`. The proof should be a single readable linear monadic case split, with the static and non-static subbranches following the same pattern and invoking `extcall_success_continuation_sound_cond_driver_ih` at the success tail.

#### Not to try
Do not resurrect `extcall_expr_sound_from_generated_driver_ih`, `extcall_generated_driver_ih_def`, or `extcall_generated_driver_ih_elim_expr`; E0109 showed this creates a >4KiB generated-prefix obligation. Do not use broad `gvs[..., AllCaseEqs()]` over the whole ExtCall prefix, and do not manually instantiate dozens of prefix variables with `qspecl_then`/`MATCH_MP` plumbing. Do not edit evaluator definitions or files outside `semantics/prop`.

#### Argument
The ExtCall expression proof splits into the already-disposed place-expression half and the result half. For the result half, unfold `evaluate_def` only for this ExtCall call and evaluate the monadic chain in order: argument evaluation; target/value extraction; calldata build; account/code checks; transient-storage retrieval; external run; success check; account/transient updates; final continuation. Every failed operation returns an error constructed by `raise`, `check`, `lift_option`, or `lift_option_type`, so those branches close immediately with `no_type_error_result_def` after the relevant local simplification and do not need induction.

On successful argument evaluation, use the generated `eval_exprs` IH to obtain state/account preservation and `exprs_runtime_typed`; then use `extcall_static_args_runtime_typed_dest` or `extcall_nonstatic_args_runtime_typed_dest` to obtain concrete target/value witnesses. On successful `run_ext_call`, use `run_ext_call_accounts_well_typed` to obtain `accounts_well_typed accounts'`. The remaining tail after the success check and updates is exactly the interface of `extcall_success_continuation_sound_cond_driver_ih`.

The optional-driver IH must not be reconstructed from a generated-prefix predicate. Instead, when proving the conditional premise required by `extcall_success_continuation_sound_cond_driver_ih`, assume the branch-local facts `returnData = []` and `IS_SOME drv`, then specialize the generated recursive `eval_expr cx (THE drv)` IH directly with the concrete post-update state and result from the current branch. `well_typed_opt env drv` plus `IS_SOME drv` and the ExtCall `well_typed_expr_def` facts provide the driver well-typedness needed by the tail helper.

#### Definition design
Do not add a new generated-prefix predicate or adapter. The accepted boundary definition for this subtree is the already-proved local theorem `extcall_success_continuation_sound_cond_driver_ih`, whose important interface is the compact premise:

`returnData = [] /\ IS_SOME drv ==> !env0 st0 res0 st0'. ... eval_expr cx (THE drv) st0 = (res0,st0') ==> ...`

That premise deliberately mentions only the final continuation condition, not all prior ExtCall prefix states. A valid proof demonstrates that the generated optional-driver IH can be connected to this compact premise by a short branch-local specialization after the prefix has been split. Failure sign: if the proof needs `extcall_generated_driver_ih_def`, a long `qspecl_then` list over prefix variables, or broad whole-prefix `AllCaseEqs()` cleanup, the interface has regressed to E0109 and the executor must stop.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. First delete the obsolete local `extcall_generated_driver_ih_def` and `extcall_generated_driver_ih_elim_expr` block if it is still present and unused. Then replace the body of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` with the direct linear proof. Reuse existing local helpers near the ExtCall helper section; do not move code to other theories and do not edit evaluator/semantics definitions. After the proof builds, update the state/plan progress if required and commit without GPG signing.

### C0.2.1.1.1: Remove obsolete generated-prefix ExtCall driver artifacts
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The generated-prefix predicate and eliminator are local, unused outside the failed approach, and harmful because they invite the forbidden E0109 proof shape. Deleting unused local theorems is mechanical and build-checkable.
- Supersedes: extcall_generated_driver_ih_def, extcall_generated_driver_ih_elim_expr
- Carries progress/evidence from: E0109
- Invalidates prior progress/evidence: generated-prefix driver adapter route

#### Progress note
This cleanup is a direct consequence of E0109: artifacts that encode the failed generated-prefix interface should no longer be available to downstream proof attempts.

#### Summary
- Delete `extcall_generated_driver_ih_def` and `extcall_generated_driver_ih_elim_expr` from `vyperTypeStmtSoundnessScript.sml` if still present.
- Confirm no remaining references to those names in `semantics/prop`.
- This cleanup prevents accidental fallback to the forbidden generated-prefix adapter route.
- The expected build state after deletion should remain at the prior placeholder baseline except for removal of unused local artifacts.

#### Description
Remove the block beginning at `Definition extcall_generated_driver_ih_def` and the immediately following theorem `extcall_generated_driver_ih_elim_expr`. They are not the accepted interface for the direct proof and were the source of the long prefix-specialization failure. If deletion reveals an unexpected live dependency, stop and report it as a design issue rather than adapting consumers to the deleted interface.

#### Statement
No theorem statement. Source cleanup in `semantics/prop/vyperTypeStmtSoundnessScript.sml`: delete obsolete local symbols `extcall_generated_driver_ih_def` and `extcall_generated_driver_ih_elim_expr`.

#### Approach
Use grep/audit after deletion for `extcall_generated_driver_ih`. A successful audit has no occurrences. The build should not require proof changes for these unused local artifacts.

#### Not to try
Do not keep the definitions “just in case” and do not add smaller eliminators around them. The whole generated-prefix predicate is the wrong abstraction, not merely an inconvenient theorem shape.

### C0.2.1.1.2: Prove `Expr_Call_ExtCall_result` by linear ExtCall prefix splitting
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: The proof is standard once constrained to one monadic operation at a time. Existing helpers cover the semantic obligations after each successful split, and all error branches are immediate no-TypeError closures. The tail driver connection is handled by C0.2.1.1.3.
- Dependencies: C0.2.1.1.1
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T081233Z_m2455_t001
- Invalidates prior progress/evidence: old C0.2.1.1 proof body using generated-prefix driver helper

#### Progress note
TO_m2455 showed the copied prefix/error skeleton is buildable with only the success-tail driver obligations left. This component reuses that evidence but changes the tail interface to the compact conditional helper, avoiding the failed generated-prefix proof.

#### Summary
- Replace the current blocked/placeholder `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` proof with a direct branch-by-branch proof.
- Unfold only this ExtCall evaluator (`Once evaluate_def`) and the monadic primitives needed for the current operation.
- Invoke the generated `eval_exprs` IH immediately after `eval_exprs cx es st` succeeds.
- Split static and non-static argument decoding with `extcall_static_args_runtime_typed_dest` and `extcall_nonstatic_args_runtime_typed_dest`.
- In all prefix error cases, close with `no_type_error_result_def`; do not leave accumulated unresolved prefix cases.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]: ... QED` — closes the result half of the ExtCall expression case of `eval_all_type_sound_mutual`, except that the success-tail method is specified by dependent child C0.2.1.1.3 and must be implemented in the same proof.

#### Approach
Start from the suspended ExtCall result goal, strip assumptions, move the ExtCall `well_typed_expr` and evaluation equation into the goal, and simplify with `Once well_typed_expr_def`, `Once evaluate_def`, `bind_def`, `ignore_bind_def`, `check_def`, `assert_def`, `return_def`, `raise_def`, `lift_option_type_def`, `lift_option_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, and `update_transient_def` only as needed. Case-split `eval_exprs`; in the `INR` case use the generated `eval_exprs` IH and `no_type_error_result_def`, and in the `INL vs` case derive `exprs_runtime_typed env es vs`. For `is_static` use `extcall_static_args_runtime_typed_dest`; for non-static use `extcall_nonstatic_args_runtime_typed_dest`; then split calldata/account/code/transient/run/success in order and close failures immediately.

#### Not to try
Do not do one giant `gvs[AllCaseEqs()]` over the entire ExtCall evaluator. Do not attempt to prove an upfront unconditional driver IH before splitting the prefix. Do not apply `extcall_expr_sound_from_generated_ih` if that forces recovering the optional-driver IH from the top-level context before the branch is concrete.

### C0.2.1.1.3: Discharge ExtCall success tail with branch-local optional-driver IH
- Kind: `proof_step`
- Risk: 2
- Work priority: 2
- Work units: 3
- Rationale: This is the precise maintainer-approved unblocking step: specialize the generated optional-driver IH only after the proof has reached the single concrete success continuation branch. The target helper’s premise is compact and should be discharged without exposing prefix witnesses.
- Dependencies: C0.2.1.1.2
- Checkpoint: yes
- Supersedes: C0.2.1.1@E0109
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T081233Z_m2458_t001, TO_type_system_rewrite-20260601T081233Z_m2460_t001
- Invalidates prior progress/evidence: manual generated-prefix qspecl specialization

#### Progress note
The failed tail-specialization evidence identifies exactly what not to do. The current component keeps the success-tail idea but requires the proof to match the compact conditional interface instead of the long generated-prefix predicate.

#### Summary
- At each successful `run_ext_call` branch, prove `accounts_well_typed accounts'` with `run_ext_call_accounts_well_typed`.
- Invoke `extcall_success_continuation_sound_cond_driver_ih` for the post-success continuation.
- Prove its conditional driver premise locally under `returnData = [] /\ IS_SOME drv`.
- Specialize the generated `eval_expr cx (THE drv)` IH with the concrete post-update state and current `res,st'`.
- Use `well_typed_opt env drv` and `IS_SOME drv` to expose the well-typed driver expression; let the tail helper handle ABI-return and driver-result shape details.

#### Statement
Within `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`, the success continuation obligation should reduce to an application of `extcall_success_continuation_sound_cond_driver_ih` with its compact conditional driver premise, not a generated-prefix premise.

#### Approach
After destructing `run_ext_call` to `SOME (success,returnData,accounts',tStorage')` and the success check to the `success = T` path, derive `accounts_well_typed accounts'` by `drule_all run_ext_call_accounts_well_typed`. Apply `extcall_success_continuation_sound_cond_driver_ih` with `runtime_consistent_def`, the existing `functions_well_typed`, `well_typed_opt`, `well_formed_type`, and driver return-type facts from the ExtCall typing assumptions. For the conditional premise, introduce `returnData=[]` and `IS_SOME drv`, case/analyze `drv` only enough to rewrite `THE drv`, then use the generated recursive IH for the driver expression at the concrete post-update state; avoid mentioning any earlier prefix state variables.

#### Not to try
Do not open `extcall_generated_driver_ih_def`; it should have been deleted. Do not manually instantiate an IH over variables named like `s_args`, `s_check`, `st_calldata`, `s_run`, etc. If the goal shown before proving the conditional premise contains the whole ExtCall prefix rather than just the compact driver continuation premise, stop and report risk mismatch.

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
