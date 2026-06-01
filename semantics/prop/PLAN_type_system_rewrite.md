# PLAN

## Structured Components

### C0: Type system rewrite task
- Kind: `task`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.1.1.2.2.1 risk 3. The static branch-local wrapper is not a straightforward low-risk proof as planned: using the broad eliminator still requires a long generated-prefix witness list, while direct `irule` does not match the conclusion. Under the task instruction and proof-hygiene checkpoint, this should be redesigned rather than tuned.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0

#### Progress note
Ancestor included only to satisfy dotted component hierarchy; no whole-task strategy change is intended.

#### Summary
Carry-forward task root. The current review changes only the ExtCall proof-refactor subtree C0.1.1.2 after E0044 showed a local proof-interface mismatch.

### C0.1: Type soundness proof repair
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.1.1.2.2.1 risk 3. The static branch-local wrapper is not a straightforward low-risk proof as planned: using the broad eliminator still requires a long generated-prefix witness list, while direct `irule` does not match the conclusion. Under the task instruction and proof-hygiene checkpoint, this should be redesigned rather than tuned.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1

#### Progress note
Included as explicit parent; no sibling work is changed.

#### Summary
Carry-forward ancestor for the active type-soundness rewrite. E0044 does not invalidate work outside C0.1.1.2.

### C0.1.1: Expression/result mutual proof repair
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.1.1.2.2.1 risk 3. The static branch-local wrapper is not a straightforward low-risk proof as planned: using the broad eliminator still requires a long generated-prefix witness list, while direct `irule` does not match the conclusion. Under the task instruction and proof-hygiene checkpoint, this should be redesigned rather than tuned.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1

#### Progress note
Included as explicit parent; strategy outside C0.1.1.2 is unchanged.

#### Summary
Carry-forward ancestor. The repair is local to the ExtCall result helper/Resume interface.

### C0.1.1.1: Carry forward audit of the ExtCall helper interface
- Kind: `proof_interface_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This audit was already completed and remains relevant: the replacement strategy depends directly on the existing local helper theorem and place-elimination lemma found by the audit.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.1, E0034

#### Progress note
The prior audit is still valid under the direct-helper strategy.

#### Summary
No new executor work. Preserve the audited fact that `extcall_expr_sound_from_generated_ih` has the right boundary shape for ExtCall expression soundness and that `type_place_expr_Call_ExtCall_NONE` closes the place conjunct. Downstream work should rely on these names rather than rediscovering the ExtCall prefix.

#### Approach
No action required unless the build reports that one of the theorem names is not in scope. If that happens, stop and report the exact missing-name error rather than editing definitions.

#### Not to try
Do not repeat the audit by broad grepping or modifying the helper theorem; this component is carried forward as completed context.

### C0.1.1.2: Close ExtCall result with a matching helper and tiny Resume entry
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The previous low-risk leaf failed because the Resume goal shape is generated-IH assumptions followed by the expression-result implication; direct unfolding at the Resume entry creates huge prefix goals. The repaired decomposition moves ExtCall branch splitting into one local helper whose assumptions match the Resume after folding the generated driver IH predicate, then leaves the Resume proof as a small helper application.
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.0, C0.1.1.2.1, C0.1.1.2.2, E0048, E0049, E0050, E0051
- Invalidates prior progress/evidence: C0.1.1.2.3@stuck, C0.1.1.2.4@old-plan, C0.1.1.2.5@old-plan

#### Progress note
Carries forward the build-clean skeleton, generated-driver predicate/eliminator, and cleanup. E0051 is accepted as evidence that the old direct-linearization/later-driver-IH split was wrong.

#### Summary
- Accept E0051 as a real risk mismatch.
- Do not unfold `well_typed_expr` or the ExtCall evaluator in the Resume entry.
- Add one helper whose hypotheses include `extcall_generated_driver_ih` and the argument-list IH.
- Prove it by adapting the existing ExtCall helper and using the conditional-driver success-continuation lemma in concrete success branches.
- Replace the Resume cheat by folding the generated IH predicate and applying the helper.
- Finish with a narrow build/hygiene audit.

#### Argument
The generated mutual IH supplies a prefix-conditional driver IH, useful only after the evaluator proof reaches the concrete success continuation containing all prefix equations. Therefore the monadic case split belongs in a local helper, not in the Resume entry. Inside the helper, evaluate arguments, close error branches immediately, use the static/nonstatic runtime-typed destination lemmas, and in each successful `run_ext_call` branch combine `run_ext_call_accounts_well_typed`, `extcall_generated_driver_ih_elim_expr`, and `extcall_success_continuation_sound_cond_driver_ih`. The Resume entry then only folds the generated prefix assumption into `extcall_generated_driver_ih` and applies the helper.

#### Definition design
`extcall_generated_driver_ih` is an opacity boundary for the enormous generated optional-driver IH. Its consumer boundary is `extcall_generated_driver_ih_elim_expr`, used only inside concrete success branches with the prefix equations already available. Failure signs: `AllCaseEqs()` over the entire ExtCall prefix, broad top-level `simp`/`gvs`, or new long prefix-adapter theorems at the Resume site.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place the new helper after `extcall_generated_driver_ih_elim_expr` if it depends on that theorem and before the `Resume` block. Replace only the `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` cheat body.

### C0.1.1.2.0: Build-clean skeleton state is carried forward
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0048 established that failed wrapper insertion was removed and the theory returned to a build-clean cheat skeleton.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.0, E0048

#### Progress note
Unchanged carry-forward component included because the ancestor subtree is replaced.

#### Summary
The failed wrapper insertion remains removed. No cleanup is needed before the repaired helper plan.

### C0.1.1.2.1: Opaque generated-driver predicate remains available infrastructure
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0049 proved the predicate and eliminator; they remain valid as a controlled boundary for the generated optional-driver IH.
- Dependencies: C0.1.1.2.0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.1, E0049

#### Progress note
Carried forward with narrowed intended use: eliminate only inside concrete success branches.

#### Summary
`extcall_generated_driver_ih_def` and `extcall_generated_driver_ih_elim_expr` remain valid local infrastructure. Do not build new long prefix-adapter theorem families.

### C0.1.1.2.2: Abandoned wrapper-adapter path remains deleted
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: E0050 audited/removed the obsolete wrapper-adapter path; the replacement plan does not revive it.
- Dependencies: C0.1.1.2.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.2, E0050

#### Progress note
Unchanged carry-forward component included because the ancestor subtree is replaced.

#### Summary
The stale wrapper-adapter proof path remains invalidated. The new helper is a direct ExtCall expression-result soundness helper.

### C0.1.1.2.3: Use a matching helper for ExtCall result instead of direct Resume linearization
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The failed direct leaf is replaced by two lower-risk obligations: prove a helper with the right interface and apply it at the Resume entry.
- Dependencies: C0.1.1.2.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0051
- Invalidates prior progress/evidence: C0.1.1.2.3@stuck

#### Progress note
E0051 diagnosed the old leaf as the wrong proof shape; this replacement preserves the no-broad-simplification insight but changes the helper interface.

#### Summary
Replace the stuck direct Resume proof with a local helper plus a small entry proof. The helper owns the ExtCall evaluator branch split and generated-driver IH consumption. The Resume entry only folds the generated IH predicate and applies the helper.

#### Argument
The helper has enough local context to perform the linear monadic proof without exploding the Resume goal. It receives `extcall_generated_driver_ih` as a hypothesis and, after branch splitting reaches each successful `run_ext_call`, extracts the conditional driver IH using `extcall_generated_driver_ih_elim_expr`. That conditional premise is passed to `extcall_success_continuation_sound_cond_driver_ih`.

#### Definition design
The helper statement should match Resume assumptions after folding the first generated prefix assumption with `GSYM extcall_generated_driver_ih_def`; it must not require hand-supplying all generated prefix witnesses at the Resume site.

#### Code structure
Add the helper in the ExtCall helper section, then edit only the `Expr_Call_ExtCall_result` Resume body.

### C0.1.1.2.3.1: Prove ExtCall result helper with generated-driver predicate hypothesis
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: This is a copy/refactor of `extcall_expr_sound_from_generated_ih`: same argument split and error branches, but the driver-IH input is `extcall_generated_driver_ih` and the success branches use the conditional-driver continuation theorem.
- Dependencies: C0.1.1.2.2
- Checkpoint: yes
- Carries progress/evidence from: C0.1.1.2.1, E0049

#### Progress note
Uses carried-forward generated-driver infrastructure; replaces old direct-linearization work.

#### Statement
Add a local theorem, suggested name `extcall_expr_sound_from_generated_driver_ih`, with conclusion matching `extcall_expr_sound_from_generated_ih` but with hypotheses:

```sml
env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
accounts_well_typed st.accounts /\ functions_well_typed cx /\
well_typed_expr env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) /\
extcall_generated_driver_ih cx es is_static func_name arg_types drv /\
(!env0 st0 res0 st0'.
   well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\ state_well_typed st0 /\
   context_well_typed cx /\ accounts_well_typed st0.accounts /\ functions_well_typed cx /\
   eval_exprs cx es st0 = (res0,st0') ==>
   state_well_typed st0' /\ env_consistent env0 cx st0' /\
   accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
   case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T) /\
eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st')
```

and the standard result postcondition for that same `Call`.

#### Approach
Start from the existing `extcall_expr_sound_from_generated_ih` proof body. Keep its `well_typed_expr` unfolding inside the helper, argument IH application, static/nonstatic branches, destination lemmas, and immediate error closures. In each successful `run_ext_call` branch, use `irule extcall_success_continuation_sound_cond_driver_ih`; prove its conditional-driver premise from `extcall_generated_driver_ih_elim_expr` only after the branch has concrete prefix equations for the argument result, target, value selection, calldata, accounts/code/tstorage, run result, success check, and state updates.

#### Not to try
Do not unfold `extcall_generated_driver_ih_def` at the start and manually instantiate all prefix variables. Do not use `AllCaseEqs()` or broad `gvs` over the whole ExtCall prefix. Do not use `extcall_success_continuation_sound`, which requires an unconditional driver IH unavailable from the generated mutual theorem.

### C0.1.1.2.3.2: Replace the ExtCall result Resume cheat by folding and applying the helper
- Kind: `proof`
- Risk: 1
- Work priority: 10
- Work units: 3
- Rationale: Once the helper exists, the Resume proof is assumption management and a helper application, avoiding the timeout sites in E0051.
- Dependencies: C0.1.1.2.3.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0051
- Invalidates prior progress/evidence: C0.1.1.2.4@old-plan

#### Progress note
Absorbs the old separate driver-IH application component because the helper already performs that work inside concrete success branches.

#### Statement
Replace the existing `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]: cheat QED` with a proof using `extcall_expr_sound_from_generated_driver_ih`.

#### Approach
Before destructing the Resume antecedents, fold the leading generated prefix-IH antecedent with `rewrite_tac[GSYM extcall_generated_driver_ih_def]` so it becomes an `extcall_generated_driver_ih` hypothesis. Strip antecedents only; avoid splitting the postcondition before helper application. Then apply `extcall_expr_sound_from_generated_driver_ih` with the visible `cx env st res st' is_static' func_name arg_types ret_type es drv` and close premises from assumptions with `first_assum ACCEPT_TAC` or small `simp`.

#### Not to try
Do not start with `reverse conj_tac`; this Resume is not the place-result branch. Do not unfold `well_typed_expr_def` or evaluator definitions in the Resume body. Do not blindly `rpt strip_tac` if it starts splitting the desired conjunctive postcondition. Do not recover the driver premise by broad prefix simplification.

### C0.1.1.2.4: Final ExtCall result build and forbidden-shape audit
- Kind: `proof_audit`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: After the helper and Resume proof build, only a mechanical build/hygiene audit remains. The old separate driver-IH application leaf is intentionally removed.
- Dependencies: C0.1.1.2.3.2
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.5
- Invalidates prior progress/evidence: C0.1.1.2.4@old-plan, C0.1.1.2.5@old-plan

#### Progress note
Reclassifies the old final audit as the only remaining post-proof work.

#### Summary
Build the theory after replacing the ExtCall result Resume cheat. Audit that the proof does not use broad top-level prefix simplification, `AllCaseEqs()` over the whole ExtCall prefix, new long generated-prefix adapters, or edits outside `semantics/prop`. Confirm that the optional driver IH is specialized only inside the helper's concrete success branches.

#### Approach
Run/build normally and inspect the helper/Resume body for the forbidden proof shapes from the maintainer clarification and E0051. Escalate if the proof required a new broad adapter theorem or top-level generated-prefix witness plumbing.

#### Not to try
Do not treat a build as sufficient if the proof violates the clarified architecture. Do not broaden scope to RawCallTarget or other remaining cheats.

### C0.1.2: Prove the focused static ExtCall success continuation
- Kind: `theorem_proof`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: After C0.1.1, the static branch should no longer require generated-prefix reconstruction: expression-list soundness, target decoding, calldata/run/update success facts, and `value_opt = NONE`/`arg_vals = TL vs` are local assumptions. Existing continuation helpers handle the remaining preservation/result typing.
- Dependencies: C0.1.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.2

#### Summary
Discharge the static success placeholder produced by C0.1.1. Use local success assumptions plus `run_ext_call_accounts_well_typed` and `extcall_success_continuation_sound_cond_driver_ih`. Specialize the generated optional-driver IH only under `returnData = [] /\ IS_SOME drv`.

#### Approach
Work only inside the focused static Resume/placeholder. First derive `accounts_well_typed accounts'` from the successful `run_ext_call`; then invoke the conditional-driver continuation helper. Error-prefix reasoning should no longer appear in this component.

#### Not to try
Do not unfold the entire ExtCall evaluator or reconstruct static prefix facts; C0.1.1 must have made them local.

### C0.1.3: Prove the focused nonstatic ExtCall success continuation
- Kind: `theorem_proof`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: After C0.1.1, the nonstatic branch has explicit successful target and transfer amount decoding. Existing helper `extcall_nonstatic_args_runtime_typed_dest` and continuation lemmas make the remainder mirror static.
- Dependencies: C0.1.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.3

#### Summary
Discharge the nonstatic success placeholder produced by C0.1.1. Use local assumptions for `SOME amount`, argument tail, successful call/update facts, and conditional driver IH. The proof mirrors the static success continuation with value transfer present.

#### Approach
Work only inside the focused nonstatic placeholder. Derive account well-typedness from `run_ext_call_accounts_well_typed`, then apply the conditional-driver continuation helper. Keep optional-driver specialization branch-local and conditional.

#### Not to try
Do not redo nonstatic prefix splitting here; C0.1.1 owns all target/value decoding and monadic prefix cases.

### C0.2: Prove RawCallTarget mutual expression case
- Kind: `theorem_proof`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: Downstream call-target branch remains a known cheat, but should be standard after ExtCall because the mutual theorem infrastructure and raw-call builtin typing lemmas are already present. It depends on the ExtCall checkpoint so the executor does not split attention before the current blocker is resolved.
- Dependencies: C0.1.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2@previous

#### Summary
- After ExtCall is proved, remove the `eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` cheat.
- Follow the existing call-expression proof style and raw-call helper lemmas.
- Keep edits in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- Do not start this before the ExtCall checkpoint closes.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` must be proved without `cheat`.

#### Approach
Use the same mutual-theorem assumptions and evaluator unfolding pattern as adjacent call cases, but only after ExtCall is closed. Mine existing raw-call local helper lemmas before introducing new ones.

#### Not to try
Do not work on RawCallTarget while ExtCall remains blocked; doing so violates the task priority and risks hiding the central proof-boundary issue.

### C0.3: Discharge raw_call_return_type_well_formed arithmetic/type lemma
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 2
- Work units: 3
- Rationale: The remaining cheat is localized to `vyperTypeBuiltinsScript.sml` and appears to be arithmetic/type-formation cleanup around `word_size`, `type_slot_size`, and the `flags.rcf_max_outsize < dimword(:256)` bound. No semantic redesign is involved.
- Dependencies: C0.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.3@previous

#### Summary
- Remove the localized `raw_call_return_type_well_formed` cheat in `semantics/prop/vyperTypeBuiltinsScript.sml`.
- Prove the arithmetic/type well-formedness obligations directly.
- Keep any helper lemmas local unless they are already useful elsewhere.
- Run focused builds after the proof.

#### Statement
`raw_call_return_type_well_formed` as currently stated in `semantics/prop/vyperTypeBuiltinsScript.sml`, without changing evaluator or semantics definitions.

#### Approach
Inspect the current theorem statement and unfold only the relevant raw-call return type and well-formedness definitions. Use existing arithmetic libraries/lemmas for word-size and dimword inequalities; do not broaden the builtin typing interface.

#### Not to try
Do not modify raw-call semantics or builtin typing definitions to make this lemma easier unless a separate unprovability report is produced.

### C0.4: Update task status files and make unsigned progress commit after cheats are removed
- Kind: `status_update_commit`
- Risk: 1
- Work priority: 3
- Work units: 2
- Rationale: Mechanical repository hygiene required by the task once proofs are complete. It does not affect theorem truth, but must obey the no-outside-semantics/prop and no-GPG constraints.
- Dependencies: C0.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.4@previous

#### Summary
- Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and/or `STATE_type_system_rewrite.md` to reflect completed proofs.
- Audit that source edits stayed under `semantics/prop`.
- Commit with `git commit --no-gpg-sign` only.
- Do not commit before proof obligations are actually discharged.

#### Statement
Repository/status action, not a HOL theorem.

#### Approach
Use `git status` to confirm paths, update task memory accurately, and commit only relevant `semantics/prop` changes. The commit message should mention ExtCall/RawCallTarget/builtin cheat removal if all are completed.

#### Not to try
Do not use default `git commit` if it may GPG-sign. Do not include unrelated files outside `semantics/prop`.

### C0.5: Final zero-cheat validation for vyperSemanticsHolTheory
- Kind: `validation`
- Risk: 1
- Work priority: 4
- Work units: 2
- Rationale: Mechanical final check specified by the task and plan. It depends on all known reachable cheats being removed first.
- Dependencies: C0.4
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5@previous

#### Summary
- Run `holbuild build vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.
- If focused builds pass but final reachable-cheat audit finds a new in-scope cheat, stop and report/re-plan.
- This is the task completion checkpoint.

#### Statement
Validation target: `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable fresh-stack CHEAT warnings.

#### Approach
Run the final build after all source cheats in scope are removed and committed/statused as appropriate. Record exact output in the task state.

#### Not to try
Do not treat `vyperTypeStmtSoundnessTheory` alone as final validation; the task completion scope is `vyperSemanticsHolTheory` reachable-cheat cleanliness.
