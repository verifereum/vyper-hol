# PLAN

## Structured Components

### C0: Type system rewrite task
- Kind: `task`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: This review only repairs the active ExtCall subtree; ancestor risk is bounded by the repaired subtree risk.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0

#### Progress note
Ancestor included only to satisfy dotted component hierarchy; no whole-task strategy change is intended.

#### Summary
Carry-forward task root. The current review changes only the ExtCall proof-refactor subtree C0.1.1.2 after E0044 showed a local proof-interface mismatch.

### C0.1: Type soundness proof repair
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The only reviewed issue is inside the ExtCall result branch; no sibling/cousin strategy is invalidated.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1

#### Progress note
Included as explicit parent; no sibling work is changed.

#### Summary
Carry-forward ancestor for the active type-soundness rewrite. E0044 does not invalidate work outside C0.1.1.2.

### C0.1.1: Expression/result mutual proof repair
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: ExtCall result remains plausible with a narrower driver-IH boundary; no broader mutual-proof redesign is required.
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

### C0.1.1.2: Close ExtCall result using branch-local opaque-driver boundaries
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The opaque predicate boundary is proved, but E0044 showed the consumer-facing broad eliminator was too hard to use inside the monolithic helper. Splitting the generated-driver premise into static/nonstatic success-tail eliminators makes the remaining proof interface match the continuation lemma.
- Supersedes: C0.1.1.2
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.0, C0.1.1.2.1, E0042, E0043
- Invalidates prior progress/evidence: C0.1.1.2.2, E0044

#### Progress note
The subtree keeps completed cleanup and predicate work, but invalidates the failed monolithic-helper leaf as a proof-interface design.

#### Summary
- Keep `extcall_generated_driver_ih` opaque during all prefix/error splitting.
- Carry forward E0042 build-clean cleanup and E0043 predicate/eliminator.
- Add two branch-local success-tail eliminators whose conclusions exactly match the conditional driver premise of `extcall_success_continuation_sound_cond_driver_ih`.
- Retry the expression helper using those lemmas; no generated-prefix witness reconstruction in the helper.
- Finish the ExtCall Resume only after the helper checkpoint succeeds.

#### Description
E0044 is accepted as a risk mismatch/stuck episode: the monolithic helper reached the static success tail but deriving the conditional driver premise forced brittle `MATCH_MP_TAC extcall_generated_driver_ih_elim_expr`/`qexistsl` plumbing. The repair is not tactic tuning; it narrows the boundary seen by the expression helper.

#### Approach
Prove the static branch-local eliminator first, then nonstatic. Then copy the old linear helper proof but discharge success-tail driver premises with the new branch-local lemmas. Finally package the generated IH into the opaque predicate at the Resume packaging point and apply the helper.

#### Not to try
Do not continue tuning the E0044 monolithic success-tail proof. Do not unfold `extcall_generated_driver_ih_def` in the expression helper or Resume. Do not use direct `irule`/`MATCH_MP_TAC extcall_generated_driver_ih_elim_expr` or long generated-prefix `qexistsl` outside the branch-local eliminator lemmas. Do not recover the driver premise by broad `simp`/`gvs` or `AllCaseEqs()` over the whole ExtCall prefix.

#### Argument
ExtCall soundness is linear through argument evaluation, target/value decoding, calldata construction, account/transient reads, external call, and success continuation. Prefix/error cases close by definitions and existing typing facts. In a run-success branch, the only nonlocal fact is the optional-driver IH, which is guarded by the exact generated prefix. Therefore the proof must specialize that generated prefix only after the branch is concrete, then expose a normal conditional IH premise to `extcall_success_continuation_sound_cond_driver_ih`.

#### Definition design
`extcall_generated_driver_ih` remains the opaque package for the generated prefix. `extcall_generated_driver_ih_elim_expr` remains an internal implementation lemma, not a consumer API. The new API consists of static and nonstatic success-tail eliminators quantified only over branch-local facts (`eval_exprs`, target/value decode, calldata, code check, run result). Their conclusion must retain the full antecedent with `context_well_typed cx` and `functions_well_typed cx`; E0044 showed weakened conclusions do not match the continuation lemma cleanly.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Insert the two branch-local eliminators immediately after `extcall_generated_driver_ih_elim_expr`. Insert the new `extcall_expr_sound_from_generated_prefix_driver_pred[local]` after them and before the Send/Selfdestruct helper region if convenient. Update only `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` downstream. Do not edit evaluator/semantics definitions or files outside `semantics/prop`.

### C0.1.1.2.0: Buildable skeleton cleanup is complete
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0042 already restored a build-clean source state; no direct work remains.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.0, E0042

#### Progress note
Cleanup remains valid.

#### Summary
Carry forward the completed buildable skeleton cleanup. Preserve the E0043 source state before adding new lemmas.

#### Approach
No action unless later edits accidentally reintroduce stale failed helper code.

#### Not to try
Do not revive `extcall_expr_sound_from_generated_prefix_delayed_ih` or the reverted E0044 helper body.

### C0.1.1.2.1: Opaque generated-driver IH predicate and broad eliminator are complete
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 1
- Work units: 0
- Rationale: E0043 proved the predicate and broad eliminator; these remain valid internal infrastructure.
- Dependencies: C0.1.1.2.0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.1, E0043

#### Progress note
E0043 boundary is retained.

#### Summary
Carry forward `extcall_generated_driver_ih_def` and `extcall_generated_driver_ih_elim_expr`. The broad eliminator is now an implementation detail for narrower branch-local lemmas.

#### Statement
Already proved:
```sml
Definition extcall_generated_driver_ih_def: ... End
Theorem extcall_generated_driver_ih_elim_expr[local]: ...
```

#### Approach
No new work. Later branch-local lemmas may use the broad eliminator internally; downstream consumers must not.

#### Not to try
Do not broaden this eliminator or use it directly in the expression helper success tails.

### C0.1.1.2.2: Prove branch-local generated-driver success-tail eliminators
- Kind: `infrastructure_lemma_group`
- Risk: 2
- Work priority: 2
- Work units: 0
- Rationale: The child lemmas isolate generated-prefix witness specialization and expose conclusions matching the continuation lemma, avoiding the E0044 consumer mismatch.
- Dependencies: C0.1.1.2.1
- Supersedes: C0.1.1.2.2
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.1, E0043
- Invalidates prior progress/evidence: E0044

#### Progress note
Replaces the failed monolithic expression-helper obligation with a narrower boundary interface.

#### Summary
- Replace the stuck monolithic helper leaf with static/nonstatic boundary lemmas.
- Static lemma handles `run_ext_call ... NONE ... = SOME (T,returnData,accounts',tStorage')`.
- Nonstatic lemma handles decoded amount and `run_ext_call ... (SOME amount) ... = SOME (T,returnData,accounts',tStorage')`.
- Both conclude the exact conditional optional-driver IH needed by `extcall_success_continuation_sound_cond_driver_ih`.

#### Approach
Static first; then copy for nonstatic with the extra value decode. Use targeted monad-definition simplification, not broad context cleanup.

#### Not to try
Do not prove one conditional theorem over `is_static`; branch separation is intentional. Do not push `qexistsl` over prefix states into consumers.

#### Argument
After branch splitting, the generated prefix facts are determined by simple monad definitions. The two child lemmas package those facts once so the expression helper can reason with ordinary branch assumptions.

#### Definition design
Do not expose generated `s_*` state variables in these theorem statements. Quantify only natural branch-local variables. Keep the conclusion full: antecedent includes `env_consistent`, `state_well_typed`, `context_well_typed`, `accounts_well_typed`, `functions_well_typed`, and the `eval_expr` equation before `well_typed_expr`.

#### Code structure
Place these lemmas immediately after `extcall_generated_driver_ih_elim_expr`, marked `[local]`. Witness plumbing is allowed inside these lemmas only.

### C0.1.1.2.2.1: Static success-tail driver-IH eliminator
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: The static success branch has direct facts for `NONE`, `TL vs`, account/transient state, and run result; the lemma statement matches the E0044 static tail context.
- Dependencies: C0.1.1.2.1
- Carries progress/evidence from: C0.1.1.2.1, E0043

#### Progress note
New static boundary lemma extracted from the E0044 failure.

#### Summary
Prove a narrow static eliminator from branch facts to the full conditional driver IH. This is the only static lemma that may reconstruct generated-prefix witnesses.

#### Statement
```sml
Theorem extcall_generated_driver_ih_elim_expr_static_success[local]:
  !cx es func_name arg_types drv st vs args_st target_addr calldata returnData accounts' tStorage'.
    extcall_generated_driver_ih cx es T func_name arg_types drv /\
    eval_exprs cx es st = (INL vs,args_st) /\
    vs <> [] /\ dest_AddressV (HD vs) = SOME target_addr /\
    build_ext_calldata (get_tenv cx) func_name arg_types (TL vs) = SOME calldata /\
    ~NULL (lookup_account target_addr args_st.accounts).code /\
    run_ext_call cx.txn.target target_addr calldata NONE args_st.accounts args_st.tStorage
      (vyper_to_tx_params cx.txn) = SOME (T,returnData,accounts',tStorage') ==>
    (returnData = [] /\ IS_SOME drv ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
       accounts_well_typed st0.accounts /\ functions_well_typed cx /\
       eval_expr cx (THE drv) st0 = (res0,st0') ==>
       well_typed_expr env0 (THE drv) ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)
```

#### Approach
Apply `extcall_generated_driver_ih_elim_expr` internally or unfold/specialize the predicate with witnesses corresponding to the static monad path. Simplify `check_def`, `lift_option_type_def`, `lift_option_def`, `return_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, and `update_transient_def` locally.

#### Not to try
Do not omit `context_well_typed cx` or `functions_well_typed cx` from the conclusion. Do not leave this proof obligation for the expression helper.

### C0.1.1.2.2.2: Nonstatic success-tail driver-IH eliminator
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: The nonstatic branch is the static shape plus decoded value; explicit assumptions determine the generated prefix without exposing `s_*` witnesses.
- Dependencies: C0.1.1.2.2.1
- Carries progress/evidence from: C0.1.1.2.1, E0043

#### Progress note
New nonstatic boundary lemma.

#### Summary
Prove a narrow nonstatic eliminator with decoded target, decoded amount, calldata over `TL (TL vs)`, and run result with `SOME amount`. It concludes the same full conditional driver IH.

#### Statement
```sml
Theorem extcall_generated_driver_ih_elim_expr_nonstatic_success[local]:
  !cx es func_name arg_types drv st vs args_st target_addr amount calldata returnData accounts' tStorage'.
    extcall_generated_driver_ih cx es F func_name arg_types drv /\
    eval_exprs cx es st = (INL vs,args_st) /\
    vs <> [] /\ TL vs <> [] /\
    dest_AddressV (HD vs) = SOME target_addr /\ dest_NumV (HD (TL vs)) = SOME amount /\
    build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL vs)) = SOME calldata /\
    ~NULL (lookup_account target_addr args_st.accounts).code /\
    run_ext_call cx.txn.target target_addr calldata (SOME amount) args_st.accounts args_st.tStorage
      (vyper_to_tx_params cx.txn) = SOME (T,returnData,accounts',tStorage') ==>
    (returnData = [] /\ IS_SOME drv ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
       accounts_well_typed st0.accounts /\ functions_well_typed cx /\
       eval_expr cx (THE drv) st0 = (res0,st0') ==>
       well_typed_expr env0 (THE drv) ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)
```

#### Approach
Copy the static proof and add local simplification for `check (TL vs <> [])`, `lift_option_type (dest_NumV (HD (TL vs)))`, and `return (SOME amount,TL (TL vs))`.

#### Not to try
Do not combine with static by an `if is_static` theorem; do not expose generated prefix states in the statement.

### C0.1.1.2.3: Prove the ExtCall expression helper using branch-local driver eliminators
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 3
- Work units: 5
- Rationale: With branch-local driver-premise lemmas available, the helper should be a linear copy of the old ExtCall helper and no longer needs generated-prefix witness plumbing.
- Dependencies: C0.1.1.2.2
- Checkpoint: yes
- Supersedes: C0.1.1.2.2
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.1, E0043
- Invalidates prior progress/evidence: E0044

#### Progress note
Same semantic helper obligation as the failed leaf, but with repaired branch-local boundary dependencies.

#### Summary
- Prove `extcall_expr_sound_from_generated_prefix_driver_pred[local]`.
- Keep `extcall_generated_driver_ih` opaque through prefix/error cases.
- In success tails, apply `extcall_success_continuation_sound_cond_driver_ih` and discharge the conditional driver premise with the static/nonstatic boundary lemma.
- No direct broad eliminator use or generated-prefix `qexistsl` in this helper.

#### Statement
```sml
Theorem extcall_expr_sound_from_generated_prefix_driver_pred[local]:
  !cx env st res st' is_static func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    extcall_generated_driver_ih cx es is_static func_name arg_types drv /\
    well_typed_expr env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) /\
    (!env0 st0 res0 st0'.
       well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\ functions_well_typed cx /\
       eval_exprs cx es st0 = (res0,st0') ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv | INR _ => T
```

#### Approach
Use the old `extcall_expr_sound_from_generated_ih` as structural template: split argument evaluation, static/nonstatic branch, calldata/code/run failure cases, and success cases linearly. In each success case derive `accounts_well_typed accounts'` with `run_ext_call_accounts_well_typed`, apply `extcall_success_continuation_sound_cond_driver_ih`, instantiate only the simple continuation witnesses (`accounts'`, `args_st`, `returnData`, `tStorage'`), and prove the conditional driver premise via `drule_all extcall_generated_driver_ih_elim_expr_static_success` or `..._nonstatic_success`.

#### Not to try
Do not use `MATCH_MP_TAC extcall_generated_driver_ih_elim_expr`, direct `irule extcall_generated_driver_ih_elim_expr`, long generated-prefix `qexistsl`, or `extcall_generated_driver_ih_def` unfolding in this helper. Do not drop `context_well_typed`/`functions_well_typed` from the driver premise.

### C0.1.1.2.4: Apply the predicate-based ExtCall helper in the final Resume
- Kind: `proof`
- Risk: 2
- Work priority: 4
- Work units: 3
- Rationale: Once the helper checkpoint succeeds, the Resume should only package the generated IH into the opaque predicate and invoke the helper.
- Dependencies: C0.1.1.2.3
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.3

#### Progress note
This replaces the old downstream Resume leaf by depending on the repaired helper checkpoint.

#### Summary
- Finish `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`.
- Package the generated optional-driver IH as `extcall_generated_driver_ih` at the generated-prefix point.
- Apply `extcall_expr_sound_from_generated_prefix_driver_pred`.
- Avoid broad prefix recovery in the Resume.

#### Statement
Target location:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:
  ...
QED
```

#### Approach
Use the existing Resume skeleton. Unfold `extcall_generated_driver_ih_def` only to package the generated premise as the atomic predicate, then apply the expression helper. The Resume should not call branch-local eliminators directly.

#### Not to try
Do not use broad `simp`/`gvs`, `AllCaseEqs()` cleanup over the whole ExtCall prefix, or generated-prefix adapter theorems. If the Resume needs to inspect static/nonstatic success tails, stop and escalate because C0.1.1.2.3's interface is wrong.

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
