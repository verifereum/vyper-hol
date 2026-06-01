# PLAN

## Structured Components

### C0: Type-system rewrite remaining proof obligations
- Kind: `proof_subtree_parent`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C0.2.2 risk 3. C0.2.2 was expected to be a straightforward linear nonstatic Resume proof, but the success tail still cannot consume the generated optional-driver IH locally without nontrivial matching/adapter work. Per the task instruction and PLAN not-to-try constraints, stop rather than continue tactic search.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, E0133

#### Progress note
Carry forward the existing top-level task plan; refine only the C0.2.1.3 static ExtCall subtree in response to E0133.

#### Summary
Top-level type-system rewrite plan remains in force. E0133 does not show a semantic counterexample or whole-task design failure. The static ExtCall branch needs a local proof-interface repair: use branch-local generated-IH specialization rather than top-level compact helper application. Work remains confined to `semantics/prop`.

#### Argument
The overall proof strategy remains mutual type soundness by cases, with ExtCall handled by linear monadic splitting and local preservation lemmas for accounts/state updates. The reviewed failure affects only the static ExtCall consumer point where a helper was applied too early; it does not change the semantic invariant or evaluator definitions.

#### Definition design
No definitions change. Definition/proof interfaces should continue to avoid exposing evaluator internals except in local ExtCall branch proofs. For generated mutual IHs, consumers must match the generated guarded shape at the branch where the guard is available; do not manufacture global compact IHs from generated prefixes.

#### Code structure
All executable edits remain under `semantics/prop`, principally `vyperTypeStmtSoundnessScript.sml`. Do not edit evaluator/semantics definitions. Group documentation-only updates into a single doc commit if any are needed.

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

### C0.2: ExtCall-related type soundness repair path
- Kind: `proof_subtree_parent`
- Risk: 3
- Work priority: 20
- Work units: 0
- Rationale: Derived from child component C0.2.2 risk 3. C0.2.2 was expected to be a straightforward linear nonstatic Resume proof, but the success tail still cannot consume the generated optional-driver IH locally without nontrivial matching/adapter work. Per the task instruction and PLAN not-to-try constraints, stop rather than continue tactic search.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2, E0133

#### Progress note
Carry forward the narrowed ExtCall strategy; refine the static success subbranch only.

#### Summary
ExtCall work continues under the maintainer-approved constraints. Static branch completion must come before nonstatic branch work. The failed top-level helper application is replaced by a branch-local proof shape. No evaluator definitions or files outside `semantics/prop` are touched.

#### Argument
ExtCall soundness is proved by splitting the evaluator monad one operation at a time. Error branches preserve state and close directly; success branches use run-ext-call preservation plus the optional-driver IH at the continuation point. The generated IH is valid only under the generated prefix, so the proof must reach that prefix before using it.

#### Definition design
Use boundary lemmas such as `run_ext_call_accounts_well_typed`, `env_consistent_get_tenv`, and `extcall_after_state_update_tail_sound` at the branch where their premises are concrete. Avoid adapter lemmas that restate the whole generated ExtCall prefix merely to produce a compact IH.

#### Code structure
Keep helper lemmas local in `vyperTypeStmtSoundnessScript.sml` near the ExtCall helper block. Resume edits should be minimal and local to `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` until that branch builds cleanly.

### C0.2.1: Static ExtCall result proof path
- Kind: `proof_subtree_parent`
- Risk: 3
- Work priority: 10
- Work units: 0
- Rationale: Derived from child component C0.2.1.4 risk 3. The oracle-recommended conditional driver premise probe is not straightforward: `mp_tac driver_ih >> simp[...]` over the branch-local prefix timed out. Per user/task stop instruction and PLAN not-to-try constraints, stop rather than tune broad generated-prefix simplification.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.1, C0.2.1.3.1, C0.2.1.3.2, E0132, E0133

#### Progress note
Preserves completed helper work and records E0133 as evidence against top-level compact-helper consumption.

#### Summary
Static ExtCall result proof remains the current prerequisite. Completed projection lemmas and the projected helper are retained. The consumer proof must now fill the existing Resume success-branch cheat directly. Nonstatic work remains downstream.

#### Argument
For the static branch, the argument list has target address followed by calldata args, and `value_opt = NONE`. After argument typing and calldata construction, all non-success cases return errors. On successful external call and state updates, `extcall_after_state_update_tail_sound` transfers state well-typedness through the optional-driver continuation.

#### Definition design
The projected helper validates the semantic tail reasoning but is not the direct consumer interface for the generated Resume. The generated Resume has a guarded IH; use it only after the guard/prefix has been produced by linear splitting.

#### Code structure
Do not remove or rewrite the proved helper. Fill the Resume's static success-tail `cheat` by adapting the helper proof body locally.

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

### C0.2.1.3: Close projected static ExtCall state-well-typed success obligation
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: The semantic helper work is already proved, and the stuck evidence identifies a local consumer-interface mismatch rather than a false statement. The remaining route is standard but must be executed at the correct point in the Resume: linear monadic splitting to the success branch, then branch-local use of the generated driver IH. This avoids the high-risk compact-IH adapter attempted in E0133.
- Dependencies: C0.2.1.3.1, C0.2.1.3.2
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.1.3, C0.2.1.3.1, C0.2.1.3.2, E0132, E0133

#### Progress note
Carries forward the proved projection lemmas and `extcall_static_projected_state_well_typed` from C0.2.1.3.1/C0.2.1.3.2. E0133 is accepted as negative evidence against applying that helper at the top of the Resume; it refines the consumer strategy rather than invalidating the helper theorem.

#### Summary
Static ExtCall state soundness should be closed by a linear branch-local Resume proof, not by top-level application of the projected helper. The proved helper remains evidence that the success-tail reasoning is semantically correct and supplies a script template. The generated optional-driver IH must be specialized only after the proof reaches the concrete success continuation where the ExtCall prefix assumptions are present. Error branches close immediately by `no_type_error_result_def`/monadic rewrites. Nonstatic ExtCall remains blocked until this static branch is build-clean.

#### Argument
The stuck point is not an ExtCall semantic counterexample; it is a mismatch between the consumer theorem interface and the induction theorem generated by the mutual proof. At the top of `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`, the available `driver_ih` is guarded by the generated monadic ExtCall prefix and includes both expression and place-expression conclusions. `extcall_static_projected_state_well_typed` instead asks for an unconditional compact expression-only driver IH, so applying it before unfolding the ExtCall chain forces forbidden generated-prefix adapter work. The correct invariant is branch-local: once the proof has evaluated arguments, built calldata, passed the target-code check, run the external call, checked success, updated accounts/transient storage, and reached the `returnData = []` optional-driver continuation, the generated prefix assumptions are exactly available and the expression half of `driver_ih` can be used to satisfy the tail continuation theorem. All earlier failure/revert branches return an `INR` and close directly for `state_well_typed`/no-type-error obligations as in the already-proved projected helper.

#### Definition design
No evaluator or semantics definitions change. Treat `extcall_static_projected_state_well_typed` as a validated proof-template/boundary result, not as the consumer interface for the generated Resume. The operative interface at the Resume is `extcall_after_state_update_tail_sound`, because its premises match the concrete success-tail state after accounts/transient updates. Failure sign: if the proof again tries to manufacture an unconditional `!env0 st0 res0 st0'. ...` compact driver IH at the top of the Resume, the design has regressed. Another failure sign is broad `AllCaseEqs()`/whole-prefix `gvs` over the generated ExtCall prefix; the proof should split one monadic operation at a time and keep only one success path live.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Do not edit evaluator/semantics files or files outside `semantics/prop`. Keep the already-proved local helper near lines 9868ff. Replace only the remaining `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` by a branch-local linear proof; documentation-only updates, if any, should be grouped into one doc update commit rather than committed separately.

### C0.2.1.3.1: Retain ExtCall continuation projection lemmas
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already proved in E0128 and still useful inside the new projected helper, especially `extcall_success_continuation_state_well_typed`. E0129 only showed these lemmas should not be applied directly at the old Resume tail edit point.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1.3.1, E0128

#### Progress note
The proved infrastructure remains sound and relevant; only the consumer boundary changes.

#### Summary
No new proof work. Keep the existing local continuation lemmas, including `extcall_success_continuation_sound_cond_driver_ih` and `extcall_success_continuation_state_well_typed`. They remain valid infrastructure for the helper that owns the linear static ExtCall success-tail proof. This component is carried forward from E0128.

#### Approach
Audit only if needed: confirm the lemmas still build and are located before the new projected helper. Do not rewrite them unless the new helper exposes a genuine statement mismatch.

#### Not to try
Do not use these lemmas as a direct fix at the old post-`PairCases_on x'` Resume point; the necessary tail equality is not exposed there in a matchable form.

### C0.2.1.3.2: Prove projected static ExtCall state helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The helper statement matches the already-projected Resume obligation and avoids relying on unavailable full-postcondition context. The internal proof is the maintainer-approved linear monadic ExtCall proof, with the driver IH specialized only in the concrete success continuation branch.
- Dependencies: C0.2.1.3.1
- Checkpoint: yes
- Supersedes: C0.2.1.3.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0129, C0.2.1.3.1
- Invalidates prior progress/evidence: C0.2.1.3.2

#### Progress note
Replaces the failed proof-ordering leaf with a boundary lemma designed for the actual projected goal discovered in E0129. Prior proved continuation lemmas remain dependencies.

#### Summary
Add a local theorem before the Resume blocks that concludes `state_well_typed st'` for a static ExtCall call after argument evaluation has succeeded. Assumptions should mirror the stable facts available in `Expr_Call_ExtCall_result_static`: original call evaluation equality, argument evaluation equality, `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, `exprs_runtime_typed env es vs`, `well_typed_opt env drv`, `well_formed_type env.type_defs ret_type`, static `MAP expr_type es = BaseT AddressT::arg_types`, return-driver type condition, and the original optional-driver IH. The proof unfolds the static evaluator linearly and closes error cases immediately. In the final success tail, derive `accounts_well_typed accounts'` from `run_ext_call_accounts_well_typed` and apply `extcall_success_continuation_state_well_typed`.

#### Statement
Suggested shape (adjust variable names to source):
```sml
Theorem extcall_static_projected_state_well_typed[local]:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    MAP expr_type es = BaseT AddressT::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st'
```
If the actual generated IH is conjunctive with a place-expression clause, quantify/assume that exact stronger shape and project the expression clause needed by `extcall_success_continuation_state_well_typed`.

#### Approach
Start from the call evaluation equality, unfold `Once evaluate_def` and only the monadic primitives needed for the static branch. Rewrite with `eval_exprs cx es st = (INL vs,args_st)`, destruct target address/calldata/account-code/run result one operation at a time, and close each error branch by simplification to the existing well-typed intermediate state. In the success branch, prove `accounts_well_typed accounts'` using `run_ext_call_accounts_well_typed`; then `irule extcall_success_continuation_state_well_typed`, provide `runtime_consistent env cx args_st` from `env_consistent/state_well_typed/accounts_well_typed/context` facts as in nearby lemmas, and pass a conditional driver-IH proof that only specializes the original driver IH after `returnData = [] /\ IS_SOME drv` is known.

#### Not to try
Do not phrase this helper with the huge generated prefix implication seen in E0129; that reproduces the mismatch. Do not use `AllCaseEqs()` or broad global `gvs` to mine the driver premise. Do not manually instantiate the continuation theorem with a long list of generated prefix variables from the Resume; the helper should own those variables by ordinary case splits.

### C0.2.1.3.3: Fill the static Resume success branch branch-locally
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: E0133 shows the previous Risk-1 top-level helper application is not the right interface. The new proof shape is still low-risk because the source already contains the linear split skeleton up to the exact `cheat`, and C0.2.1.3.2 has proved the same tail reasoning in a standalone theorem.
- Dependencies: C0.2.1.3.2
- Checkpoint: yes
- Supersedes: C0.2.1.3.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0132, E0133

#### Progress note
Replaces the failed consumer strategy from E0133. E0133 remains valid evidence not to apply `extcall_static_projected_state_well_typed` at the top of the Resume. E0132 carries forward as the proof template for the tail reasoning.

#### Summary
Replace the remaining static Resume `cheat` without applying `extcall_static_projected_state_well_typed` at the top. Reuse the existing explicit monadic split skeleton in the Resume. In the `success`/state-update/`returnData = []` branch, prove `accounts_well_typed accounts'` with `run_ext_call_accounts_well_typed`, establish the well-formed return type/evaluated type facts as in `extcall_static_projected_state_well_typed`, and then invoke `extcall_after_state_update_tail_sound`. Feed the generated `driver_ih` only at this branch-local point; use only the expression half needed by the tail theorem. Build must pass with the static success-tail cheat removed.

#### Description
The baseline code at lines 17499ff already performs most of the allowed linear ExtCall proof and reaches a single `cheat` after `Cases_on x'0`, with `accounts_well_typed x'2` already available. Continue from that point rather than restarting with a top-level `irule` of the projected helper. Mirror the successful proof body of `extcall_static_projected_state_well_typed` lines 9921-9938, but in the Resume context use the saved `driver_ih` directly where `extcall_after_state_update_tail_sound` needs the optional-driver continuation. The final goal for this component is only `state_well_typed st'`, not the full expression postcondition.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]:
  ...
  ==> state_well_typed st'

Concretely, remove the `cheat` in the static ExtCall success branch of `semantics/prop/vyperTypeStmtSoundnessScript.sml` and close the Resume branch.

#### Approach
Start from the current explicit skeleton, not from the failed top-level `irule extcall_static_projected_state_well_typed` attempt. After the success branch has `accounts_well_typed` for the returned accounts, reproduce the local facts from the helper proof: `runtime_consistent env cx args_st`, unfold `well_formed_type_def` to get the successful `evaluate_type`, and use `env_consistent_get_tenv` if needed. Then `irule extcall_after_state_update_tail_sound`; discharge ordinary state/account/env premises by `simp`/small `metis_tac`, and discharge the optional-driver premise by specializing the saved `driver_ih` in this already-split branch, projecting only the expression conjunct and using `well_typed_opt env drv` plus `(!e. drv = SOME e ==> expr_type e = ret_type)` as needed.

#### Not to try
Do not try `irule extcall_static_projected_state_well_typed` or `qspecl_then ... extcall_static_projected_state_well_typed` at the top of the Resume; E0133 showed this leaves the generated prefix-to-compact-IH mismatch. Do not use broad `simp`/`gvs`/`AllCaseEqs()` to recover the driver premise from the top-level Resume context. Do not build a long generated-prefix adapter theorem or use large `metis_tac[extcall_static_projected_state_well_typed, driver_ih]`; that timed out and violates the maintainer clarification.

### C0.2.1.3.4: Audit static ExtCall state branch build and remaining cheats
- Kind: `proof_audit`
- Risk: 1
- Work priority: 30
- Work units: 1
- Rationale: After the helper and Resume refactor, validation is mechanical: target theory builds and the static state-well-typed cheat is gone. Nonstatic ExtCall remains separate.
- Dependencies: C0.2.1.3.3
- Checkpoint: yes
- Supersedes: C0.2.1.3.3
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.1.3.3

#### Progress note
Replaces the previous audit leaf only to update dependencies and scope after the helper-based repair.

#### Summary
Run the target build for `vyperTypeStmtSoundnessTheory`. Confirm the explicit cheat in the static ExtCall success state branch has been removed. Confirm no files outside `semantics/prop` were edited. Do not treat the separate nonstatic ExtCall cheat as part of this component.

#### Approach
Use `holbuild` on the target theory after the edit. Inspect the static Resume region around the old line 17455 to ensure there is no remaining `cheat` for the static success state branch. If the helper proof required broad generated-prefix reconstruction, stop and escalate rather than committing.

#### Not to try
Do not start proving the nonstatic ExtCall branch in this audit. Do not make cleanup edits outside `semantics/prop`.

### C0.2.1.4: Close nonstatic ExtCall result through a compact projected-state boundary lemma
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The previous direct Resume strategy is blocked by generated-prefix pollution, but the static projected-state helper already demonstrates that moving ExtCall prefix analysis into a local theorem is viable. The nonstatic variant differs only by the value argument branch and can use the already-proved destination/nonempty helpers plus the existing success-continuation boundary.
- Supersedes: C0.2.1.4.1
- Progress transition: `replacement`
- Carries progress/evidence from: E0136
- Invalidates prior progress/evidence: C0.2.1.4.1

#### Progress note
E0136 remains valid evidence that the direct-tail leaf is blocked. Its proved small helper is retained, but the prior obligation shape is replaced by a boundary-helper decomposition.

#### Summary
Replace the failed direct-tail Resume strategy. Keep the proved nonstatic argument-shape helper from E0136. Add a local `extcall_nonstatic_projected_state_well_typed` theorem whose assumptions expose only compact facts, especially a plain generated driver IH, not the large Resume prefix. Then make `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` prove the state-well-typed result by invoking this boundary theorem after the `eval_exprs` split. Do not unfold the whole nonstatic ExtCall monad in the Resume body.

#### Approach
Rebase the nonstatic proof around a local projected-state lemma. The executor should first ensure the carried helper builds, then prove the nonstatic projected lemma by copying the proven static theorem’s structure and changing the nonstatic argument branch, and finally simplify the Resume to invoke that lemma.

#### Not to try
Do not continue the direct-tail Resume proof from E0136. Do not keep the generated optional-driver/prefix implication visible while running `gvs[return_def, raise_def]`. Do not recover the driver premise by broad simplification or generated-prefix adapter theorems; the only intended consumer of the driver IH is the compact boundary helper.

#### Argument
The nonstatic ExtCall state preservation proof should be factored at the same boundary as `extcall_static_projected_state_well_typed`. After `eval_exprs` succeeds, the argument values are runtime-typed and their expression types have shape `Address, Uint256, arg_types`; therefore `extcall_nonstatic_args_runtime_typed_dest` supplies the target address and amount, and `extcall_nonstatic_args_runtime_typed_nonempty` supplies the list nonemptiness needed to make the monadic checks compute cheaply. The prefix then either raises a non-type runtime error, preserving the current typed state, or reaches `run_ext_call`; account typing after a successful external call comes from `run_ext_call_accounts_well_typed`. The final post-update/driver/decode continuation should not be reproved in the Resume; call `extcall_success_continuation_state_well_typed`, with `runtime_consistent env cx args_st` obtained from `env_consistent`, `state_well_typed`, `context_well_typed`, and `accounts_well_typed` as in the static helper. The optional driver IH is used only at this continuation boundary, after `returnData` and `drv` are concrete, and appears in the local helper as a compact premise rather than as a generated prefix implication in the Resume simplifier context.

#### Definition design
No evaluator or semantics definitions may change. The proof interface is a local theorem, not a new semantic definition. The boundary theorem should take the successful `eval_exprs` facts, typing facts, and a compact driver-IH premise as assumptions, and conclude only `state_well_typed st'`. This avoids making consumers unfold `evaluate_def` for the full ExtCall chain. Failure sign: if the Resume body again contains broad `gvs`/`AllCaseEqs()` over the generated ExtCall prefix or a huge generated optional-driver premise, the boundary is being bypassed and the plan is not being followed.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place the new local nonstatic projected-state theorem near `extcall_static_projected_state_well_typed` and the existing nonstatic argument helpers, before the Resume block. Keep `extcall_nonstatic_args_runtime_typed_nonempty` from E0136. The Resume proof near line 17553 should be short and should call local boundary lemmas; it should not introduce new library code or edit outside `semantics/prop`.

### C0.2.1.4.1: Carry forward the nonstatic runtime-typed argument nonempty helper
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: E0136 reports that `extcall_nonstatic_args_runtime_typed_nonempty` was extracted, proved, and the file built cleanly. This helper directly supports the new projected-state lemma by avoiding inline simplification of `exprs_runtime_typed_def` in a polluted context.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0136

#### Progress note
This is the one successful artifact from the failed episode and remains useful under the replacement strategy.

#### Summary
Retain the local theorem `extcall_nonstatic_args_runtime_typed_nonempty`. Its statement should say that runtime-typed nonstatic ExtCall arguments with expression types `Address :: Uint256 :: arg_tys` imply `vs <> [] /\ TL vs <> []`. No further design work is needed; this is a carry-forward/audit step to ensure the helper remains present before proving the boundary lemma.

#### Statement
`Theorem extcall_nonstatic_args_runtime_typed_nonempty[local]:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  vs <> [] /\ TL vs <> []`

#### Approach
If the theorem is already present, leave it as-is and build/audit it. It should be proved locally from `exprs_runtime_typed_def` and list cases, outside the Resume context where the generated prefix caused timeouts.

#### Not to try
Do not inline this proof inside the Resume or inside a context containing the generated ExtCall prefix; E0136 showed that even this small fact can time out there.

### C0.2.1.4.2: Prove the nonstatic projected-state boundary lemma
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: This is a direct nonstatic analogue of the already-proved static projected-state theorem. The critical risk from E0136 is removed because the theorem has a compact explicit driver-IH premise rather than the generated Resume prefix implication.
- Dependencies: C0.2.1.4.1
- Checkpoint: yes
- Carries progress/evidence from: E0136

#### Progress note
Uses the carried nonempty helper and replaces the blocked direct-tail proof interface with a compact local theorem.

#### Summary
Add `extcall_nonstatic_projected_state_well_typed[local]`. It should assume the usual consistency/typing facts, the nonstatic `eval_expr` equality, successful `eval_exprs`, `exprs_runtime_typed env es vs`, `MAP expr_type es = Address :: Uint256 :: arg_types`, and a compact optional-driver IH premise. It concludes only `state_well_typed st'`. The proof should mirror `extcall_static_projected_state_well_typed`, using the nonstatic destination/nonempty helpers and `extcall_success_continuation_state_well_typed` for the final continuation.

#### Statement
Suggested statement shape:
```sml
Theorem extcall_nonstatic_projected_state_well_typed[local]:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    MAP expr_type es = BaseT AddressT::BaseT (UintT 256)::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st'
```

#### Approach
Copy the proof structure of `extcall_static_projected_state_well_typed`. First derive `target_addr` and `amount` with `extcall_nonstatic_args_runtime_typed_dest`, and derive `vs <> [] /\ TL vs <> []` using C0.2.1.4.1. Then move only the `eval_expr` equality to the goal and unfold one `evaluate_def` plus the monad primitives, rewrite the known `eval_exprs` result, and split the prefix one operation at a time. In the success case after `run_ext_call`, prove account typing via `run_ext_call_accounts_well_typed`, establish `runtime_consistent env cx args_st`, and invoke `extcall_success_continuation_state_well_typed` for the post-update/driver/decode tail.

#### Not to try
Do not prove this inside the Resume body. Do not use `AllCaseEqs()` or broad `gvs` over a goal that contains the huge generated prefix implication from E0136. Do not manually construct a long adapter theorem for the generated driver premise; the premise in this lemma should already match the continuation helper closely enough for `drule_all`/`irule` style use.

### C0.2.1.4.3: Resume the nonstatic ExtCall result proof using the projected-state lemma
- Kind: `proof`
- Risk: 2
- Work priority: 2
- Work units: 3
- Rationale: Once the boundary lemma exists, the Resume no longer needs to simplify the full nonstatic ExtCall chain with the generated driver IH visible. The remaining proof should be a short dispatch on the argument-evaluation result and an application of existing/local state-preservation lemmas.
- Dependencies: C0.2.1.4.2
- Checkpoint: yes
- Supersedes: C0.2.1.4.1
- Progress transition: `replacement`
- Carries progress/evidence from: E0136
- Invalidates prior progress/evidence: C0.2.1.4.1

#### Progress note
This is the new proof leaf replacing the failed direct-tail proof leaf from E0136; the old direct-tail evidence is invalidated except for the carried helper.

#### Summary
Replace the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]`. The success branch after `eval_exprs` should use `extcall_nonstatic_projected_state_well_typed`. The argument-error branch should use the existing ExtCall args-error state lemma rather than unfolding the whole call. The Resume should stay small and avoid generated-prefix simplification.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]: ... QED` with no `cheat`; this component closes the nonstatic result/state-well-typed branch required by the suspended mutual theorem.

#### Approach
Follow the shape used by nearby resumed call cases: introduce assumptions, expose the `well_typed_expr` ExtCall facts with one `well_typed_expr_def` rewrite, split `eval_exprs cx es st`. In the error branch, use `eval_extcall_args_error_state_well_typed` (or the corresponding existing args-error lemma matching the goal). In the success branch, use the mutual IH for `eval_exprs` to get `state_well_typed args_st`, `env_consistent env cx args_st`, `accounts_well_typed args_st.accounts`, `no_type_error_result (INL vs)`, and `exprs_runtime_typed env es vs`, then apply C0.2.1.4.2 with the generated optional-driver IH as the compact driver premise.

#### Not to try
Do not unfold and simplify the entire ExtCall nonstatic evaluator in the Resume after C0.2.1.4.2 exists. Do not run broad `simp`/`gvs` over the generated driver IH or large prefix. If the generated IH does not match the boundary lemma directly, adjust the boundary lemma premise locally rather than building a long theorem-plumbing script in the Resume.

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

### C0.2.2: Nonstatic ExtCall_result branch via conditional continuation helper
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The episode shows the nonstatic prefix split is straightforward and the only mismatch is the proof interface at the success tail. Existing local theorem `extcall_success_continuation_sound_cond_driver_ih` has exactly the right interface: it needs the optional-driver IH only under `returnData = [] /\ IS_SOME drv`, matching the generated prefix after the branch has been split. This avoids broad simplification and avoids a generated-prefix adapter theorem.
- Supersedes: C0.2.2
- Progress transition: `replacement`
- Carries progress/evidence from: E0134
- Invalidates prior progress/evidence: C0.2.2@old-unconditional-tail

#### Progress note
E0134's prefix-splitting work remains valid evidence, but its final unconditional-helper tail is the wrong interface. This replacement carries forward the established successful prefix path and invalidates only the old instruction to invoke `extcall_success_continuation_sound` directly.

#### Summary
- Replace the old direct `extcall_success_continuation_sound` tail with the conditional helper route.
- Keep the accepted linear nonstatic ExtCall prefix split from E0134: argument typing, calldata, account-code check, `run_ext_call ... (SOME amount)`, revert/success.
- In the single success branch, prove only the conditional driver premise required by `extcall_success_continuation_sound_cond_driver_ih`.
- Derive that conditional premise by `strip_tac` on `returnData = [] /\ IS_SOME drv`, then `mp_tac driver_ih >> simp[...]` using the already-split prefix facts; do not `qspecl` the generated prefix manually.
- The old leaf's unconditional-helper approach is invalidated; the prefix progress from E0134 still supports the new proof shape.

#### Description
This subtree closes `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` without changing semantics or files outside `semantics/prop`. The key repair is not more prefix splitting; it is using the existing conditional continuation lemma at the success tail so that the generated optional-driver IH is consumed only under the exact branch condition where it is valid.

#### Approach
Use the same branch-local linear proof skeleton from E0134 up to the success case after `Cases_on x'0`. In the success case, do not invoke `extcall_success_continuation_sound`; invoke `extcall_success_continuation_sound_cond_driver_ih` (or the state projection if the current subgoal is only `state_well_typed st'`). For its driver premise, assert `returnData = [] /\ IS_SOME drv ==> !env0 st0 res0 st0'. ...` locally by stripping the condition and then pushing the saved `driver_ih` theorem with `mp_tac driver_ih >> simp[...]`, relying on the already-present prefix equalities rather than enumerating generated variables.

#### Not to try
Do not try to recover an unconditional optional-driver IH from the suspended branch context. Do not use broad `gvs[AllCaseEqs()]` or whole-prefix simplification to make the generated prefix disappear. Do not write a long adapter theorem whose statement reproduces the generated ExtCall prefix. Do not manually `Q.SPECL` the generated prefix variable list; E0134 shows that is brittle and unnecessary if the saved `driver_ih` is pushed back to the goal after the prefix facts are in context.

#### Argument
The nonstatic ExtCall evaluator first evaluates arguments and, in the successful argument case, requires an address and value argument. The already-proved `extcall_nonstatic_args_runtime_typed_dest` gives `target_addr` and `amount`, after which the evaluator's monadic prefix is deterministic: build calldata from `TL (TL vs)`, check target code, run the external call with `SOME amount`, then either close error/revert cases immediately or enter the success continuation. The success continuation updates accounts and transient storage and then either evaluates the optional driver when `returnData = [] /\ IS_SOME drv`, or ABI-decodes `returnData`. The theorem `extcall_success_continuation_sound_cond_driver_ih` is designed for exactly this point: the ABI-decode path needs no driver IH, while the driver path needs only the generated driver IH under the same branch condition. Therefore the proof is true without manufacturing a global unconditional IH.

#### Definition design
No definition changes are permitted or needed. The proof interface is the local helper stack already in `vyperTypeStmtSoundnessScript.sml`: `extcall_nonstatic_args_runtime_typed_dest` for destructing typed nonstatic arguments, `run_ext_call_accounts_well_typed` for returned accounts, `update_accounts_transient_runtime_consistent`/`runtime_consistent_def` for the updated state, and especially `extcall_success_continuation_sound_cond_driver_ih` for the continuation. Failure sign: if the proof again requires copying or adapting the whole generated monadic prefix into a theorem statement, stop; the helper is being applied too early or the saved `driver_ih` is not being pushed with the prefix facts in scope.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Do not edit evaluator definitions or files outside `semantics/prop`. The old `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` is replaced by the linear branch proof. Any tiny local assertion for the conditional driver premise should live inside the success branch; do not add a global generated-prefix adapter theorem.

### C0.2.2.1: Probe the branch-local conditional driver premise
- Kind: `proof_probe`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: This is the exact stuck point from E0134, narrowed to a branch-local assertion. It should be low risk because the generated `driver_ih` antecedent is precisely the prefix facts that are already assumptions in the success branch; pushing the saved theorem with `mp_tac driver_ih >> simp[...]` lets HOL instantiate the generated variables instead of requiring manual `qspecl`.
- Checkpoint: yes
- Carries progress/evidence from: E0134

#### Progress note
New probe extracted from the exact E0134 stuck point; carries forward the successful prefix state that makes the conditional assertion meaningful.

#### Summary
- Edit only the nonstatic success branch in the Resume proof.
- After the `run_ext_call ... (SOME amount)` success split and account-typing fact, add a local assertion of the conditional driver IH.
- Prove it by `strip_tac` on `returnData = [] /\ IS_SOME drv`, then use the saved `driver_ih` with `mp_tac driver_ih >> simp[...]` while all generated prefix equalities are still in context.
- Do not enumerate the generated prefix variables manually.
- Checkpoint here because this is the repaired interface that de-risks the rest of the branch.

#### Description
The deliverable is not a standalone theorem; it is a successful local proof fragment inside the nonstatic Resume success case showing the premise shape required by `extcall_success_continuation_sound_cond_driver_ih`. If the current goal is already a state-only projection, the same local assertion should be sufficient for `extcall_success_continuation_state_well_typed`.

#### Statement
Local assertion inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` success branch:
```sml
returnData = [] /\ IS_SOME drv ==>
  !env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\
    context_well_typed cx /\ accounts_well_typed st0.accounts /\
    functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
    (well_typed_expr env0 (THE drv) ==>
     state_well_typed st0' /\ env_consistent env0 cx st0' /\
     accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
     case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)
```

#### Approach
Keep `driver_ih` saved by the existing `pop_last_assum (fn driver_ih => ...)`. At the success tail, before applying the continuation helper, prove the assertion with `strip_tac`; then use `mp_tac driver_ih` followed by `simp[...]` including the branch condition and the prefix definitions/equalities already exposed (`bind_def`, `return_def`, `assert_def`, `update_accounts_def`, `update_transient_def` as needed). If `simp` leaves only the desired quantified IH, accept it; if it leaves prefix obligations, add only the specific rewrite/fact for that already-split prefix operation.

#### Not to try
Do not call `first_x_assum drule_all` blindly; E0134 indicates it may pick or shape the wrong implication. Do not use explicit `Q.SPECL` over all generated variables. Do not move this into a reusable global lemma with the whole generated prefix in its statement.

### C0.2.2.2: Close and audit the nonstatic ExtCall_result Resume branch
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Once the conditional driver premise is available, the rest is a standard application of the existing continuation helper plus already-proved ExtCall facts. Error and revert branches were reported straightforward in E0134.
- Dependencies: C0.2.2.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0134
- Invalidates prior progress/evidence: C0.2.2@old-unconditional-tail

#### Progress note
This leaf refines the old C0.2.2 proof attempt by preserving the linear split and changing only the success-tail interface.

#### Summary
- Complete the nonstatic Resume proof using the C0.2.2.1 conditional driver premise.
- Use `extcall_success_continuation_sound_cond_driver_ih` for full continuation obligations, or `extcall_success_continuation_state_well_typed` if the resumed subgoal is only the state conjunct.
- Supply `accounts_well_typed accounts'` from `run_ext_call_accounts_well_typed` and runtime consistency from the argument-state facts.
- Close calldata/account-code/run failure and revert cases immediately with the local monadic rewrites.
- Final audit: `holbuild` target succeeds and the `Expr_Call_ExtCall_result_nonstatic` cheat is gone.

#### Description
This component finishes the task-scoped theorem branch after the repaired driver-premise probe succeeds. It should be a direct continuation of the E0134 proof skeleton, with the tail helper changed from unconditional to conditional.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` in `semantics/prop/vyperTypeStmtSoundnessScript.sml` has no `cheat` and the target theory builds.

#### Approach
In the final success branch, invoke the conditional continuation helper at the point where the evaluator has just performed `assert success`, `update_accounts`, and `update_transient`, with `accounts' = x'2`, base state `args_st`, `returnData = x'1`, and transient storage `x'3` (or the actual names produced by the split). Prove helper side conditions from `runtime_consistent_def`, `functions_well_typed`, `well_typed_opt`, `well_formed_type`, `(!e. drv = SOME e ==> expr_type e = ret_type)`, and the local conditional driver premise from C0.2.2.1. Use `rewrite_tac[GSYM no_type_error_result_def]` only if needed to align the postcondition goal, as in the E0134 skeleton.

#### Not to try
Do not revert to `extcall_success_continuation_sound` unless an unconditional driver IH is already directly in context. Do not broaden the proof to the whole `Expr_Call_ExtCall_result` parent theorem. Do not change semantics definitions or evaluator behavior.

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
