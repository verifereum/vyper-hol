# PLAN

## Structured Components

### C0: Carry forward baseline build/CHEAT audit
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed mechanical audit evidence remains valid and is not part of the remaining proof frontier.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0, E0530

#### Progress note
C0 is preserved as completed baseline evidence. It does not authorize stale scheduling; the remaining frontier is rebased below.

#### Summary
- Completed current-source baseline build/CHEAT audit is carried forward.
- No executor proof work remains in this component.
- Use it only as source-status context; final validation is C7.

#### Description
This component records the already-closed initial status check. The task completion criterion is still C7, not C0.

#### Statement
Build/audit baseline for the fresh stack reachable from `vyperSemanticsHolTheory`.

#### Approach
No work remains. Do not rerun unless later source changes make final validation fail and a new audit is needed.

#### Not to try
Do not treat old retired-theory cheats found during broad greps as task obligations unless C7 shows they are reachable from `vyperSemanticsHolTheory`.

### C1: Carry forward completed assignment-target state preservation and joint soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: Completed assignment-target branches and compatibility wrappers are preserved from accepted build-through evidence; no remaining C1 leaf is executable.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C1, C1.1, C1.2, C1.3, C1.4, C1.5, C1.6, E0531, E0532, E0533, E0534, E0535, E0536

#### Progress note
The assignment-target work that the TASK identified as handover-sensitive is preserved as done. The inherited update-binop CHEAT path is not part of this carry-forward; it is now owned by C3.

#### Summary
- Assignment-target state preservation and joint soundness branches are carried forward as complete.
- This includes the TopLevelVar HashMapRef/ArrayRef, ImmutableVar, TupleTargetV, assign_targets_cons, and compatibility wrapper work.
- Remaining assignment-related CHEAT warnings in the update-binop/subscript helper chain are scheduled separately under C3.
- Downstream statement proofs may use the strengthened assignment interfaces; they must not weaken them.

#### Description
No executor work remains here. If a downstream proof exposes that a completed assignment theorem still depends on a CHEAT in the update-binop path, route that work to C3 rather than reopening C1.

#### Statement
Current source-authoritative assignment-target mutual theorem and wrappers, including `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error`, remain available without weakening their strengthened assumptions.

#### Approach
Carry forward the existing proofs. Downstream components should use `drule`/`irule` against the strengthened wrappers, supplying shape and assignability side conditions from statement typing or target-runtime facts.

#### Not to try
Do not weaken `assign_target_sound_mutual` or drop `assign_target_assignable_context`. Do not inline top-level storage/hashmap/array assignment semantics in C2 statement cases.

#### Argument
The completed assignment-target theorem follows the assignment evaluator recursion and proves a joint all-result invariant: no TypeError, preservation of runtime consistency/state/accounts as appropriate, and target/value typing preservation. The strengthened side conditions `assign_operation_matches_target_shape` and `assign_target_assignable_context` remain part of the interface. Top-level storage/hashmap/array cases are discharged by branch helpers matching the semantic storage branches, while target-list cases follow the recursive `assign_targets` structure.

#### Definition design
The proof interface exported to downstream statement soundness is the strengthened assignment boundary: target runtime typing, operation runtime typing, shape matching, and assignable-context assumptions imply no TypeError and preservation. Failure signs for later consumers are attempts to unfold `assign_target_def` in statement/call proofs or to remove the strengthened side conditions. The inherited update-binop lemmas are not covered by this component and must be closed by C3 before final zero-CHEAT validation.

#### Code structure
Keep assignment target semantic proofs in `semantics/prop/vyperTypeStatePreservationScript.sml` and compatibility wrappers in `semantics/prop/vyperTypeAssignSoundnessScript.sml`. Statement proofs in `vyperTypeStmtSoundnessScript.sml` should consume these theorems, not duplicate assignment evaluator case analysis.

### C2: Fresh Vyper type-system soundness stack
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Structural parent included only to satisfy dotted component validation. This scoped update does not change C2's sibling obligations; the prior high-risk flag was inherited from the now-refined IntCall wrapper subtree, whose remaining local work is low-risk audit.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2 plan, episode:E1327

#### Progress note
Validation parent only for this scoped merge. No sibling scheduling or whole-task roadmap is changed here.

#### Summary
Structural parent for the fresh soundness stack. This update only unblocks the completed IntCall wrapper subtree by adding a focused audit leaf. Other C2 obligations remain governed by their existing components.

#### Approach
Do not begin work at this parent. Use the leaf under C2.6.4.2.5.6.4 only.

#### Not to try
Do not treat this validation parent as permission to re-plan or edit unrelated C2 siblings.

#### Argument
This scoped parent is not being redesigned. The only relevant argument carried through this update is that the former high-risk IntCall sub-branch has had all semantic children proved/reviewed, so its local residual work can be reduced to mechanical audit.

#### Definition design
No definition changes are authorized by this parent entry.

#### Code structure
No repository-wide file organization changes are authorized by this parent entry.

### C2.0: Carry forward completed C2 semantic repair and helper evidence
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: These components have already closed and are unaffected by flattening the later source-prefix repair. They establish the semantic and boundary infrastructure consumed by the remaining C2 leaves.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.0, C2.1, C2.2, C2.3, C2.4, C2.5, C2.5.1, C2.5.2, C2.5.3, E1081, E1082, E1083, E1084, E1085, E1091, E1098, E1099

#### Progress note
This leaf records that the earlier C2 proof products remain valid after the ancestor rebase. No executor work is required unless a later build proves source drift invalidated them.

#### Summary
- Carry forward the callable-body no-escaping-control definition repair.
- Carry forward projection, semantic no-escape, tail-helper, body-IH packaging, and local IntCall helper proofs.
- These are prerequisites for the remaining consumer refactor but require no new edits in this rebase.

#### Description
The executor should not reopen these proofs proactively. If holbuild later reports a failure inside one of the carried helper statements, report that exact source failure; otherwise treat the helper interface as available.

#### Statement
Carried interfaces include the strengthened `functions_well_typed`/`stmts_no_control_escape` facts and local IntCall helper lemmas already proved in the prior C2.1--C2.5 episodes.

#### Approach
No action. Use these facts as opaque boundaries in later leaves.

#### Not to try
Do not duplicate the generated evaluator induction or reprove the carried helper bodies inside the consumer branch.

### C2.6: Statement soundness obligations
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Structural parent included only to satisfy dotted component validation. The scoped IntCall child now has a low-risk audit frontier; no other statement-soundness sibling is modified by this update.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.6 plan, episode:E1327

#### Progress note
Validation parent only. Prior progress on statement soundness is carried forward; this update changes only the requested IntCall subtree.

#### Summary
Statement-soundness grouping parent. The only active change is under the IntCall wrapper verification subtree. Existing ready/done siblings are not rescheduled here.

#### Approach
Executor should descend to C2.6.4.2.5.6.4.4 for the authorized work.

#### Not to try
Do not use this parent as permission to work on AnnAssign/Assign/AugAssign or other statement cases.

#### Argument
No new statement-level induction argument is introduced here. The relevant child argument is that the IntCall wrapper proof has been factored into branch-tail helper interfaces and proved through E1327.

#### Definition design
No statement-level typing/evaluator definitions change in this update.

#### Code structure
All scoped edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.

### C2.6.0: Refactor `create_tail_result_sound_simp` to avoid whole-create-tail simplification
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: The failing block already has the two facts needed to derive the post-state invariant: an exact result equality for the explicit create-tail case expression and a `runtime_consistent` fact over the `SND` of the corresponding monadic do-expression from `create_tail_sound`. Prior holbuild evidence shows only a tactic-timeout from broad rewriting, not a missing semantic invariant. The repair is a local proof refactor with no theorem-statement or architecture change.
- Checkpoint: yes
- Supersedes: C2.6.0
- Progress transition: `refinement`
- Carries progress/evidence from: TO_type_system_rewrite-20260525T153549Z_m56407_t001, TO_type_system_rewrite-20260525T153549Z_m56418_t002, STATE_type_system_rewrite.md lines 8-19

#### Summary
Replace the timeout-prone proof block at `semantics/prop/vyperTypeStmtSoundnessScript.sml` lines 9875--9880. The target theorem is `create_tail_result_sound_simp`; its statement and `create_tail_sound` must remain unchanged. Derive `runtime_consistent env cx st'` from the existing result equality and the existing `runtime_consistent env cx (SND (... do ... st))` assumption by proving/reusing a small equality between the two result-state expressions. This component is a checkpoint because the build must pass this prefix theorem before queued IntCall continuation work can be verified.

#### Description
Current holbuild stops before the IntCall continuation area because the proof of `create_tail_result_sound_simp` unfolds the full create-tail monadic computation with `rw[bind_def, ignore_bind_def, check_def, assert_def, raise_def, return_def, lift_option_type_def, get_accounts_def, update_accounts_def] >> gvs[]`, producing a >4KB goal and timing out. The theorem has just invoked `create_tail_sound`, so after `gvs[]` the context contains both the expanded case-expression equality `(case check ... st of ...) = (res,st')` and a preservation assumption for `SND ((do ... od) st)`. Refactor only the local derivation of `runtime_consistent env cx st'`. If the later no-TypeError subproof also times out with the same pattern, apply the same equality-bridge idea there, but do not begin the separate IntCall helper/integration work under this component.

#### Statement
In `create_tail_result_sound_simp`, prove the local assertion:

```sml
`runtime_consistent env cx st'`
```

from the already available assumptions shaped like:

```sml
(case check (vs <> []) "create no args" st of ... ) = (res,st')
runtime_consistent env cx (SND ((do
  check (vs <> []) "create no args";
  amount' <- lift_option_type (SOME amount) "create value";
  target_addr' <- lift_option_type (SOME target_addr) "create target";
  accounts <- get_accounts;
  check (amount' <= (lookup_account cx.txn.target accounts).balance)
    "create insufficient balance";
  check (~account_already_created (... accounts)) "address collision";
  if amount' > 0 then transfer_value ... else return ();
  update_accounts (increment_nonce cx.txn.target);
  return (Value (AddressV ...))
od) st))
```

The theorem statement, `create_tail_sound`, and downstream IntCall theorem statements are not to be changed.

#### Approach
Use the exact result equality as a state-projection bridge, not as an invitation to simplify the whole create-tail computation. Preferred shape: assert a local claim such as `SND ((do ... od) st) = st'`, prove that claim from the result equality by a targeted monadic skeleton simplification, then rewrite the `runtime_consistent` assumption with it. Keep the simplifier list minimal and branch locally with `TOP_CASE_TAC`/small `Cases_on` only if the equality proof requires distinguishing the few `check`/`transfer_value` outcomes; close impossible branches directly from the pair equality instead of calling broad `gvs[]` on the entire monadic term. After the edit, run `holbuild build vyperTypeStmtSoundnessTheory` with the normal timeout and record whether it advances past `create_tail_result_sound_simp` to the queued IntCall area or later.

#### Not to try
Do not retry the old broad block `qpat_x_assum ... mp_tac >> qpat_x_assum ... mp_tac >> rw[bind_def, ignore_bind_def, check_def, assert_def, raise_def, return_def, lift_option_type_def, get_accounts_def, update_accounts_def] >> gvs[]`; that exact shape has timed out. Do not weaken or restate `create_tail_result_sound_simp`, do not edit `create_tail_sound`, and do not touch the final `Expr_Call_IntCall` resume or the `intcall_successful_defaults_continuation_sound_general` plan here. Do not add further dotted tactical children under this component; if this focused equality bridge still times out, close the component with evidence and request an ancestor C2.6 proof-interface rebase.

### C2.6.1: Normalize and audit the IntCall proof source after failed probes
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: E1115 says the temporary probe was removed and the failed TRY experiment was reverted, but this must be confirmed before further proof edits. The audit is mechanical and local.
- Progress transition: `refinement`
- Carries progress/evidence from: E1115

#### Progress note
Carries forward E1115's cleanup claim but requires a local source check so subsequent proof work starts from a known branch shape.

#### Summary
- Inspect `vyperTypeStmtSoundnessScript.sml` around the helper block and the failing IntCall region.
- Confirm there is no `FAIL_TAC "live_precond_residual"`, `FAIL_TAC "precond_rw_probe"`, or temporary `TRY (... >> NO_TAC)` experiment.
- Confirm `intcall_pushed_body_preconditions_live_from_defaults` is still present and saved before adding the new corollary.
- If cleanup edits are needed, keep them anchored to the exact source range, not generic text replacement.

#### Description
This component prevents stale probe edits from confusing the refactor. It should not attempt to prove the main theorem. If a build is run, it is acceptable for it to fail later at the known IntCall assertion; the closure criterion is source normalization plus no accidental probe fragments.

#### Statement
No theorem statement. Source cleanup/audit only.

#### Approach
Read the source ranges around lines ~2052-2149, ~8250-8265, and ~10930-11005. Remove only confirmed temporary probe/experiment text. Prefer exact line/range edits over global replacement.

#### Not to try
Do not use a generic `replace_text` snippet such as `(impl_tac >- simp[]) >> simp[]) >>`; prior evidence shows it can match the wrong occurrence.

### C2.6.2: Prove an exact live pushed-body precondition corollary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: This is a direct corollary of the accepted `intcall_pushed_body_preconditions_live_from_defaults`, with `src_id_opt` instantiated to `env_body.current_src`. Its conclusion exactly matches the failing pushed-body triple.
- Dependencies: C2.6.1
- Progress transition: `refinement`
- Carries progress/evidence from: E1114, E1115

#### Progress note
Refines the accepted helper into a consumer-shaped interface; the previous helper proof remains valid but should no longer be applied directly in the giant main theorem.

#### Summary
- Add a local theorem immediately after `intcall_pushed_body_preconditions_live_from_defaults`.
- The theorem should take `env_body.current_src` directly in the pushed stack, avoiding a separate `src_id_opt` premise.
- It should assume exactly the live facts listed by the failed goal: env consistency for `env cx args_st`, env_body field equalities, default-state immutables/scopes consistency, state/accounts/scope well-typedness, and the lock equation.
- It should conclude the three preconditions needed for the body IH at `(lock_st with scopes := [call_env])`.

#### Statement
```sml
Theorem intcall_live_pushed_body_preconditions[local]:
  !env env_body cx args_st dflt_st lock_st call_env fn nr is_view.
    env_consistent env cx args_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
```

#### Approach
Prove by applying `intcall_pushed_body_preconditions_live_from_defaults` with `src_id_opt = env_body.current_src`. The premise `env_body.current_src = src_id_opt` then simplifies by reflexivity; all other assumptions are identical after simplification. Keep this proof small and separate from the generated-IH context.

#### Not to try
Do not restate or unfold `intcall_pushed_body_preconditions_from_lock`, `intcall_env_body_consistency_for_defaults`, or `acquire_nonreentrant_lock` in the main IntCall theorem. Do not add extra assumptions about `sig`, `x''2`, or body typing; this corollary is only about the frame/precondition triple.

### C2.6.3: Flattened IntCall helper closure and downstream handoff
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: The only live uncertainty in this subtree was resolved by the reviewed E1232 proof: `intcall_expr_no_type_error_from_generated_ih` now builds through using the general actual-args helper. The remaining direct work in this subtree is a mechanical focused build audit; downstream proof obligations remain outside this subtree in the existing C2.6.4 component.
- Dependencies: C2.6.2
- Supersedes: C2.6.3.1, C2.6.3.2, C2.6.3.3, C2.6.3.3.1, C2.6.3.3.2, C2.6.3.3.2.4, C2.6.3.3.2.4.6
- Progress transition: `replacement`
- Carries progress/evidence from: C2.6.3.3.2.4.6, episode:E1232, tool_output:TO_type_system_rewrite-20260525T153549Z_m56129_t001, tool_output:TO_type_system_rewrite-20260525T153549Z_m56132_t001

#### Progress note
This replacement deliberately collapses the old deep helper-chain descendants into one carried-forward subtree fact. Prior proof work still counts: the source contains the accepted helper proof, and the focused build evidence reaches the downstream `eval_all_type_sound_mutual[Expr_Call_IntCall]` resume. The old fine-grained children should no longer drive scheduling.

#### Summary
- Collapse the over-deep IntCall helper-history subtree into one carried-forward proof group.
- Treat `intcall_expr_no_type_error_from_generated_ih` as a stable boundary theorem, backed by E1232.
- Keep C2.6.3.4 as the only executable leaf in this subtree: a focused build audit and handoff.
- Do not add more tactical descendants under the old generated-IH helper chain.
- Downstream `eval_all_type_sound_mutual[Expr_Call_IntCall]` integration remains the next semantic proof phase outside this flattened subtree.

#### Description
This subtree no longer owns the full downstream `Expr_Call_IntCall` proof. Its job is to preserve the completed local IntCall no-TypeError helper stack as a stable boundary and verify, by focused build, that the current source has advanced past that helper to the downstream resume. If the build again stops inside `intcall_expr_no_type_error_from_generated_ih`, that is a regression in the carried-forward boundary and should be escalated. If the build stops at `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]`, this subtree is done and the executor should move to the existing downstream integration component.

#### Approach
Use the current proved source as a boundary. The executor should not edit first; begin the leaf audit, run the focused build, and classify the stopping point. If the build reaches `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]`, close this subtree as done/progressed and proceed to the existing downstream component.

#### Not to try
Do not reopen the old NoneT-only helper path, do not add more descendants under C2.6.3.3.2.4.*, and do not tune the tail of `intcall_expr_no_type_error_from_generated_ih`. The prior failure was caused by destructing away the arbitrary return component; E1232 fixed that boundary.

#### Argument
The mathematical boundary now available is: after the IntCall evaluator has successfully looked up the module/function, evaluated actual arguments, obtained callable-body typing facts, and preserved the arbitrary return component `ret`, the helper `intcall_actual_args_success_no_type_error_from_generated_ih_general` proves the no-TypeError result for the actual-argument-success path without requiring `ret = NoneT`. The accepted proof of `intcall_expr_no_type_error_from_generated_ih` preserves the existential package from `callable_body_typing_from_env_consistent` long enough to instantiate that general helper. Therefore the remaining work inside C2.6.3 is not another induction or semantic helper: it is only to confirm the source passes this theorem and exposes the downstream mutual-theorem branch.

#### Definition design
No definitions should be changed in this subtree. The proof interface is the local helper boundary around `intcall_expr_no_type_error_from_generated_ih` and `intcall_actual_args_success_no_type_error_from_generated_ih_general`. Failure signs are: a reappearance of an obligation forcing `x''4 = NoneT`; a proof that destructs callable-body facts with broad `strip_tac`/`gvs[]` before helper application; or a focused build stopping before line 13650 in the local helper rather than at the downstream resume.

#### Code structure
All source work, if any regression is found, is local to `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the IntCall helper block around lines 13214--13650. Do not move these helpers to another theory during this subtree. The focused build target is `vyperTypeStmtSoundnessTheory`; the whole-task `vyperSemanticsHolTheory` build is not the first audit here because statement soundness is the immediate failing theory.

### C2.6.3.4: Focused build-audit and handoff after the closed IntCall helper
- Kind: `build_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is a mechanical audit of already-reviewed proof progress. The expected build failure is downstream at `eval_all_type_sound_mutual[Expr_Call_IntCall]`, not inside the local helper; no new semantic case analysis is required for this leaf.
- Checkpoint: yes
- Supersedes: C2.6.3.4
- Progress transition: `refinement`
- Carries progress/evidence from: C2.6.3.3.2.4.6, episode:E1232, tool_output:TO_type_system_rewrite-20260525T153549Z_m56129_t001

#### Progress note
The old C2.6.3.4 was a build audit but was blocked by decomposition pressure. This refined leaf keeps the same audit obligation while making the expected downstream handoff explicit and flattening away the stale helper-chain children.

#### Summary
- Begin this component before any further build/edit work on the IntCall path.
- Run `holbuild build vyperTypeStmtSoundnessTheory`.
- Success criterion for this leaf is that `intcall_expr_no_type_error_from_generated_ih` is accepted and the build either succeeds or stops later at the downstream `Expr_Call_IntCall` mutual-theorem resume.
- If the old `x''4 = NoneT` failure reappears, stop and escalate as a regression.
- Do not modify source unless the audit proves the carried-forward helper was overwritten/regressed.

#### Description
This leaf exists to unblock the PLAN gate and confirm the stable boundary after E1232. The expected focused-build transcript should match the prior evidence: the helper theorem is replayed, and holbuild resumes/fails at `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]` around line 13650, with large generated-IH assumptions. That downstream failure belongs to the next integration component, not this audit.

#### Statement
Audit obligation:
```sh
holbuild build vyperTypeStmtSoundnessTheory
```
The audit passes for this component if the build gets past `intcall_expr_no_type_error_from_generated_ih` and reaches the downstream `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]` integration point (or succeeds further).

#### Approach
Run the focused build without editing. Inspect the first failure location. If it is at line ~13650 in `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]`, close this component with the build evidence and proceed to the existing downstream integration component. If it is inside `intcall_expr_no_type_error_from_generated_ih`, compare the source around lines 13619--13636 with the E1232-controlled destruct/application pattern before making changes; escalate if the source has drifted.

#### Not to try
Do not attempt to prove the downstream `Expr_Call_IntCall` branch under this audit leaf. Do not use broad `gvs[]` or `strip_tac` rewrites in the local helper, do not prove `x''4 = NoneT`, and do not reintroduce the old `intcall_actual_args_success_no_type_error_from_generated_ih` call.

### C2.6.4: Call-expression statement soundness obligations
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Structural parent included only to satisfy dotted component validation. The local IntCall wrapper subtree has been de-risked to audit-only after E1327.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.6.4 plan, episode:E1327

#### Progress note
Validation parent only; no sibling call-expression obligations are changed.

#### Summary
Call-expression grouping parent. This update only concerns the live IntCall wrapper verification branch. Other call-expression work remains outside this augment scope.

#### Approach
Proceed only to the new audit leaf under C2.6.4.2.5.6.4.

#### Not to try
Do not re-open external call/special call work from this parent.

#### Argument
The relevant mathematical argument is localized in the IntCall wrapper child: branch-specific helper theorems avoid duplicating evaluator case analysis and transport generated IHs into the call-body context.

#### Definition design
No call-expression definitions change here.

#### Code structure
Keep local helper theorems near the IntCall proof in `vyperTypeStmtSoundnessScript.sml`.

### C2.6.4.1: Add an all-result default-argument frame package for IntCall
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: This is a strengthening of the already-proved default-result package, using the same default generated IH plus `finally` scope-restoration/frame facts. It is standard preservation plumbing and local to the default-evaluation phase.
- Carries progress/evidence from: E1237

#### Progress note
Builds on the repaired default-IH selector from E1237/E1238 but proves a stronger consumer-shaped package instead of only success/no-TypeError facts.

#### Summary
- Prove a local helper for default-argument `finally` evaluation.
- Conclusion must include `state_well_typed dflt_st`, caller-frame `env_consistent env cx dflt_st`, `accounts_well_typed dflt_st.accounts`, and `no_type_error_result dflt_res` for both success and failure.
- In the success case, preserve existing package facts needed later: default values runtime typed, `call_env`, `scope_well_typed call_env`, `env_scopes_consistent`, and immutable consistency.
- The helper should hide default `finally`/scope manipulation from later proofs.

#### Statement
Suggested local theorem: `intcall_defaults_result_frame_package_from_generated_ih_general[local]`. Use the exact side-condition block from `intcall_defaults_result_package_from_generated_ih_general`, but strengthen the conclusion to:

```sml
state_well_typed dflt_st /\
env_consistent env cx dflt_st /\
accounts_well_typed dflt_st.accounts /\
no_type_error_result dflt_res /\
case dflt_res of
| INL dflt_vs =>
    exprs_runtime_typed (defaults_env env_body)
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) dflt_vs /\
    ?call_env.
      bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
      scope_well_typed call_env /\
      env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
      env_immutables_consistent env_body
        (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st
| INR _ => T
```

#### Approach
Start from the proof of `intcall_defaults_result_package_from_generated_ih_general` and keep its call to `intcall_default_exprs_sound_from_generated_ih`. After destructing that result, add caller-frame preservation facts using the same scope-restoration facts already used by default soundness helpers; the default `finally` restores `args_st.scopes`, and context/function well-typedness are stack-insensitive. In the `INL` branch, reuse `intcall_bind_arguments_from_runtime_typed` rather than rebuilding list-rel facts from scratch.

#### Not to try
Do not expose only `env_immutables_consistent`/`env_scopes_consistent`; downstream needs caller `env_consistent env cx dflt_st` even when defaults fail. Do not move this proof into the final resume. Do not change evaluator or default typing definitions.

### C2.6.4.2: Internal-call expression soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Structural parent included only to satisfy dotted component validation. The specific live IntCall wrapper branch has no remaining semantic proof blocker; audit remains.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.6.4.2 plan, episode:E1327

#### Progress note
Validation parent only. The scoped update does not alter sibling internal-call components.

#### Summary
Internal-call grouping parent. The completed descendants established the generated-IH transport and default-failure-tail wrapper for the live IntCall case. The only new executable work is final audit.

#### Approach
Use the child audit leaf; do not add new helpers unless the audit exposes a genuine regression.

#### Not to try
Do not duplicate the IntCall evaluator split in a new proof tree.

#### Argument
The internal-call proof follows evaluator recursion once: actual args, defaults, binding, return-type evaluation, lock/push/body/finally/cast. The scoped child has already proved the difficult default-failure/live wrapper interface; this parent adds no new case analysis.

#### Definition design
The proof interface remains helper-theorem based rather than definition-changing.

#### Code structure
No file split changes; helper theorems stay local to `vyperTypeStmtSoundnessScript.sml`.

### C2.6.4.2.1: Repair the prefix no-TypeError consumer via a post-push body-IH boundary
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The stuck evidence identifies a proof-interface mismatch, not a false statement. The replacement decomposes the large theorem into statement-preserving adapters whose premises match the live assumptions.
- Progress transition: `refinement`
- Carries progress/evidence from: E1247, TO_type_system_rewrite-20260525T153549Z_m56721_t001, TO_type_system_rewrite-20260525T153549Z_m56728_t001, TO_type_system_rewrite-20260525T153549Z_m56730_t001, TO_type_system_rewrite-20260525T153549Z_m56737_t001, TO_type_system_rewrite-20260525T153549Z_m56739_t001

#### Progress note
E1247's stuck evidence is accepted and used to refine the same local obligation. Prior failed tactic attempts justify replacing the proof interface with local adapters.

#### Summary
Keep the statement of `intcall_default_success_general_post_lock_consumer_no_type_error` unchanged. Stop proving generated-IH premises inside the large theorem. Extract the generated six-setup body-IH premise into a simple post-push body-IH lemma, prove a post-lock no-TypeError consumer over that boundary, then reprove the general consumer by lock-result cases.

#### Approach
Treat this as a proof-interface refactor. First restore the large theorem to a simple skeleton, then add the adapter and tail helper so the theorem no longer constructs existential/conjunction packages or generated-IH setup premises inline.

#### Not to try
Do not tune `qpat_x_assum`, `first_assum`, `metis_tac`, or broad `gvs` inside the large theorem. Do not use the contradiction helper. Do not introduce another `ret=NoneT` shortcut through the existing NoneT consumer; E1247 shows it exposes a huge package and can time out.

#### Argument
The body IH supplied by the generated IntCall case is stronger than the post-lock tail needs. After concrete successful default binding, return-type evaluation, lock acquisition, and `push_function`, the tail only needs a post-push premise quantified over `cxf` and `pushed_st`. E1247 shows that reconstructing this inside the large theorem causes brittle setup goals. Isolate that implication in an adapter, prove the tail over the adapter interface, and leave the large theorem as phase composition.

#### Definition design
No definitions change. The proof interface boundary is the post-push body-IH predicate, abstracting away `bind_arguments`, `evaluate_type`, and lock acquisition while preserving the `push_function` point where `eval_stmts` runs. If a child proof again needs `state_well_typed st0'` from a full generated setup implication inside the large theorem, the interface is being bypassed.

#### Code structure
All work stays in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near `intcall_default_success_post_lock_no_type_error_from_body_ih` and `intcall_default_success_general_post_lock_consumer_no_type_error`. Add local theorems immediately before the general consumer. Remove the experimental `ret=NoneT` split if present; replace it with the lock-result split using the new helpers.

### C2.6.4.2.1.1: Clean up the experimental general-consumer proof body
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: Mechanical cleanup guided by E1247: remove unbuilt experimental branches before adding boundary lemmas.
- Carries progress/evidence from: E1247

#### Summary
Replace the current partial proof of `intcall_default_success_general_post_lock_consumer_no_type_error` with a simple skeleton or temporary sketch while adding helpers. The final subtree must have no cheat here. Remove the experimental `ret=NoneT` consumer shortcut and any contradiction-helper delegation.

#### Statement
Source cleanup only; theorem statement remains exactly the current source statement of `intcall_default_success_general_post_lock_consumer_no_type_error`.

#### Approach
Edit only the proof text around the general consumer. The desired final proof will case-split on `lock_res`; the successful branch calls the new post-push-tail helper, and the failure branch uses `intcall_lock_no_type_error_result`.

#### Not to try
Do not try to make the old proof pass before adding helpers. Do not unfold evaluator/monad definitions in the large theorem.

### C2.6.4.2.1.2: Extract the generated setup IH to a post-push body IH
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Pure implication plumbing over existing assumptions and equalities; all hard body-soundness facts come from the supplied generated IH.
- Dependencies: C2.6.4.2.1.1
- Carries progress/evidence from: E1247

#### Summary
Prove a local lemma that consumes the generated six-setup body-IH package and the concrete successful setup equalities, returning the two-argument post-push body-IH premise needed by the tail. The conclusion should quantify only `cxf' pushed_st'` and then the body evaluation variables.

#### Statement
Add a local theorem `intcall_generated_body_ih_to_post_push_body_ih` whose premises are: the generated six-setup body-IH implication, concrete successful `bind_arguments`, `evaluate_type`, and lock equalities. Its conclusion is `!cxf' pushed_st'. push_function (env_body.current_src,fn) call_env cx lock_st = (INL cxf',pushed_st') ==> !env1 ret_ty1 env2 st0 res0 st0'. ...body soundness conclusion...`. Use the exact body-soundness conclusion from `intcall_default_success_post_lock_no_type_error_from_body_ih`.

#### Approach
After `rpt strip_tac`, specialize the generated IH with `call_env`, `bind_st`, `ret_st`, `lock_st`, `cxf'`, and `pushed_st'`. Discharge its setup antecedent using the three concrete equalities and the post-push assumption, then specialize it to the body-evaluation variables.

#### Not to try
Do not include monadic continuation result assumptions or `res/st'` in this lemma. Do not unfold `bind_arguments`, `evaluate_type`, `push_function`, or `eval_stmts`; the lemma is only about using the supplied implication.

### C2.6.4.2.1.3: Prove post-lock no-TypeError from the post-push body IH
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This is the existing post-lock proof with the generated-setup premise already abstracted away. It should call the existing tail lemma directly.
- Dependencies: C2.6.4.2.1.2
- Checkpoint: yes
- Carries progress/evidence from: E1247

#### Summary
Add a local theorem `intcall_default_success_post_lock_no_type_error_from_post_push_body_ih` with the same post-lock monadic no-TypeError conclusion as `intcall_default_success_post_lock_no_type_error_from_body_ih`, but with a simple post-push body-IH premise instead of the generated six-setup premise. Delegate to `intcall_default_success_lock_success_tail_no_type_error`.

#### Statement
The statement should match `intcall_default_success_post_lock_no_type_error_from_body_ih` after removing the bind/eval/lock setup premises and replacing the generated first premise with the post-push body-IH premise from C2.6.4.2.1.2. Use the same tail monadic equality and conclude `no_type_error_result res`.

#### Approach
Mirror the proof of `intcall_default_success_post_lock_no_type_error_from_body_ih` from its tail-lemma application onward, but skip `intcall_body_ih_after_setup_success` because the first premise already has the post-push shape. Discharge frame/environment assumptions by `first_assum ACCEPT_TAC` plus small existing rewrites such as `env_scopes_consistent_stk_irrelevant`.

#### Not to try
Do not call `intcall_default_success_post_lock_no_type_error_from_body_ih`; that reintroduces the six-setup premise. Do not prove safe-cast typing or full continuation preservation here.

### C2.6.4.2.1.4: Finish the general post-lock consumer using the post-push boundary
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Once the adapter and post-push tail theorem exist, the original large theorem is a straightforward lock-result split with no generated-IH reconstruction in the theorem body.
- Dependencies: C2.6.4.2.1.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E1247

#### Summary
Prove `intcall_default_success_general_post_lock_consumer_no_type_error` unchanged. In the `lock_res = INL ()` branch, derive the post-push body IH using `intcall_generated_body_ih_to_post_push_body_ih` and apply `intcall_default_success_post_lock_no_type_error_from_post_push_body_ih`. In the `lock_res = INR e` branch, use `intcall_lock_no_type_error_result`.

#### Statement
Current source theorem statement of `intcall_default_success_general_post_lock_consumer_no_type_error`; do not change it.

#### Approach
Start with `rpt gen_tac >> strip_tac >> Cases_on lock_res`. For `INL`, destruct unit if needed, obtain the post-push premise from C2.6.4.2.1.2 and apply the post-push tail theorem. For `INR`, use the existing lock no-TypeError result path as in the NoneT consumer lock-failure branch.

#### Not to try
Do not split on `ret = NoneT`; the post-push boundary is uniform. Do not reconstruct the first premise of `intcall_default_success_post_lock_no_type_error_from_body_ih` inline. Do not unfold the full monadic tail in this large theorem.

### C2.6.4.2.2: Package lock-attempt frame and no-TypeError facts
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Small case split over `nr`/`nonreentrant_slot`; existing lock no-TypeError and frame lemmas cover the hard facts.
- Dependencies: C2.6.4.2.1
- Carries progress/evidence from: E1240

#### Progress note
Packages existing local lock-frame progress for the full continuation theorem.

#### Summary
Add `intcall_lock_attempt_sound_frame[local]` consuming the lock equation once and returning `state_well_typed lock_st`, `accounts_well_typed lock_st.accounts`, `no_type_error_result lock_res`, and failure-branch caller env preservation. Strengthen to all-branch env preservation if easy.

#### Statement
Suggested theorem:

```sml
Theorem intcall_lock_attempt_sound_frame[local]:
  !env cx nr is_view dflt_st lock_res lock_st.
    env_consistent env cx dflt_st /\ state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    (if nr then case cx.nonreentrant_slot of NONE => raise (Error (RuntimeError "nonreentrant slot missing")) | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view else return ()) dflt_st = (lock_res,lock_st) ==>
    state_well_typed lock_st /\ accounts_well_typed lock_st.accounts /\
    no_type_error_result lock_res /\
    (case lock_res of INL _ => T | INR _ => env_consistent env cx lock_st)
```

#### Approach
Case split on `nr` and `cx.nonreentrant_slot`. Use `intcall_lock_no_type_error_result` for no-TypeError and `intcall_lock_state_preserves_frame`/related frame lemmas for success. Runtime-error branches should simplify to unchanged/frame-equivalent state.

#### Not to try
Do not unfold state/account well-typed definitions in the large continuation theorem; prove the package here.

### C2.6.4.2.3: Prove IntCall safe-cast value result typing
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Isolates a small definitional `expr_result_typed` fact using existing safe-cast typing lemmas.
- Dependencies: C2.6.4.2.1

#### Progress note
Needed because no-TypeError-only helpers cannot solve the final full result-typing goal.

#### Summary
Add `intcall_safe_cast_expr_result_typed[local]` turning `safe_cast ret_tv rv = SOME crv` plus IntCall static return-type facts into `expr_result_typed env (Call ... IntCall ...) (Value crv)`. This hides `expr_result_typed_def`/`expr_runtime_typed_def` from larger proofs.

#### Statement
Suggested theorem:

```sml
Theorem intcall_safe_cast_expr_result_typed[local]:
  !env loc src_id_opt fn es extra ret_ty ret_tv rv crv.
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret_ty /\
    evaluate_type env.type_defs ret_ty = SOME ret_tv /\
    safe_cast ret_tv rv = SOME crv ==>
    expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) (Value crv)
```

#### Approach
Unfold `expr_result_typed_def` and `expr_runtime_typed_def` only here. Use `safe_cast_well_typed`/safe-cast preservation to get `value_has_type ret_tv crv`; discharge hashmap-place side conditions by simplification or `well_typed_expr_not_hashmap_place`.

#### Not to try
Do not unfold result-typing definitions in the full continuation theorem. Keep explicit `expr_type`/`evaluate_type` premises that callers can supply.

### C2.6.4.2.4: Frame restoration after internal-call finalization
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward parent context only; the local proof now has a clear two-case argument.
- Progress transition: `carry_forward`
- Carries progress/evidence from: prior C2.6.4.2.4 plan

#### Progress note
Included only as explicit parent context. Omitted siblings remain unchanged.

#### Summary
Parent context for frame-restoration obligations around `finally` and cleanup. The repair targets the no-fallthrough outer-INR branch.

#### Argument
The finalizer can return `INR` either after normal body success plus cleanup failure, or after a body exception plus cleanup. No-fallthrough eliminates the normal-success case; the exception case is handled by the body IH and cleanup frame restoration.

#### Definition design
Keep finalizer case analysis inside local boundary helpers so consumers do not unfold monadic plumbing.

#### Code structure
Use the existing cleanup and environment restoration lemmas; do not move proofs between theory files.

### C2.6.4.2.4.1: Wrap cleanup-after-pop frame restoration for an arbitrary cleanup result
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already proved in E1262 and unaffected by the E1266 interface mismatch.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.6.4.2.4.1@E1262

#### Progress note
Carry forward the existing local theorem `intcall_cleanup_after_body_preserves_caller_frame`; no source changes are planned here.

#### Summary
Keep the cleanup wrapper lemma unchanged. It composes cleanup-after-pop preservation with caller-frame restoration. It is a prerequisite for both branches of the outer-INR helper.

#### Statement
Existing local theorem `intcall_cleanup_after_body_preserves_caller_frame[local]` in `vyperTypeStmtSoundnessScript.sml`.

#### Approach
No action unless the replacement edit accidentally breaks this theorem. If touched, restore the E1262 proof by composing `intcall_cleanup_after_pop_preserves_frame` and `intcall_cleanup_frame_restore_sound`.

#### Not to try
Do not inline this restoration argument in later consumers; this lemma is the intended boundary.

### C2.6.4.2.4.2: Classify outer finally returning INR into body and cleanup equations
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: Already proved in E1263; it is a pure definitional classifier and is independent of exception return typing.
- Dependencies: C2.6.4.2.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.6.4.2.4.2@E1263

#### Progress note
Carry forward the classifier theorem unchanged; it remains the right proof boundary for the repaired helper.

#### Summary
Keep the outer-finally INR classifier unchanged. It splits the semantic equation into normal-body/cleanup-fails and body-exception/cleanup-after-body cases. The repaired preservation helper should still start by applying this classifier.

#### Statement
Use the existing local theorem `intcall_finally_try_handle_inr_body_cleanup_cases` in `vyperTypeStmtSoundnessScript.sml`.

#### Approach
No action expected. If a rebuild exposes drift, repair only by unfolding `finally_def`, `try_def`, `handle_function_def`, monad definitions, and case equations; do not introduce typing assumptions.

#### Not to try
Do not merge classification with preservation; keeping this pure avoids repeated monad case analysis.

### C2.6.4.2.4.3: Repair outer-INR finally preservation helper to consume the ordinary generated body IH
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The revised statement exactly matches the live IH in `intcall_default_success_post_push_sound`; the existing E1264 proof body already specializes that IH at `env_body,NoneT,env_after`, which is the correct way to obtain `NoneT` exception typing for this concrete body run.
- Dependencies: C2.6.4.2.4.1, C2.6.4.2.4.2
- Checkpoint: yes
- Supersedes: C2.6.4.2.4.3-old, E1264-old-helper-interface
- Progress transition: `replacement`
- Carries progress/evidence from: C2.6.4.2.4.3@E1264 proof skeleton, C2.6.4.2.4.4@E1266 mismatch evidence
- Invalidates prior progress/evidence: C2.6.4.2.4.3@E1264 as completed old statement

#### Progress note
This is a statement/interface replacement, not a new mathematical idea. Prior E1264 tactics remain useful but do not close the new component until rebuilt with the repaired statement.

#### Summary
Replace the first premise of `intcall_default_finally_inr_preserves_frame` with the ordinary generated IH. Its exceptional branch must conclude `return_exception_typed env_exn ret_ty1 exn`, not `return_exception_typed env_exn NoneT exn`, under arbitrary `ret_ty1`. Inside the proof, specialize the IH at `env_body`, `NoneT`, and `env_after` for the actual body evaluation. Keep the theorem name if possible to minimize consumer edits.

#### Statement
Preferred repaired local statement: keep the current `intcall_default_finally_inr_preserves_frame[local]` statement unchanged except in the first generated-IH premise, where the exceptional branch conclusion is:

```sml
return_exception_typed env_exn ret_ty1 exn
```

instead of:

```sml
return_exception_typed env_exn NoneT exn
```

All other premises/conclusion remain as in current source.

#### Approach
Edit the theorem statement first. Then reuse the current proof: apply `intcall_finally_try_handle_inr_body_cleanup_cases`; in both body cases invoke the first assumption with `env_body`, `NoneT`, `env_after`, `lock_st with scopes := [call_env]`, and the concrete body result/state. The exceptional branch will now still yield `return_exception_typed env_exn NoneT body_exn` because the specialization uses `ret_ty1 = NoneT`. Finish both branches with `intcall_cleanup_after_body_preserves_caller_frame` and static fields from `type_stmts_env_preserved_static` or `env_extends_def`.

#### Not to try
Do not keep the old helper premise and try to prove it in the consumer. Do not add a no-control precondition to this helper; the needed `NoneT` typing comes from specializing the IH with `NoneT`, and no-control does not rule out `ReturnException`. Do not change `intcall_default_success_post_push_sound`'s statement.

### C2.6.4.2.4.4: Focused default-success outer-finalizer branches
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Carry-forward parent context only; E1282 narrowed the branch to a single frame triple.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E1282

#### Progress note
Included as parent for the local replacement. The solved INL branch progress is carried forward.

#### Summary
Parent context for the final focused branches of `intcall_default_success_post_push_sound`. The INL/safe-cast branch is solved; the remaining work is the outer-INR frame triple.

#### Argument
The proof should preserve the solved INL branch and redirect only the remaining outer-INR frame obligation to a boundary lemma with the correct return-type interface.

#### Definition design
The boundary should be tested by whether the consumer no longer sees a `type_stmts ... NoneT ...` subgoal in the no-fallthrough branch.

#### Code structure
Edit only the local helper region and the final outer-INR branch of the theorem.

### C2.6.4.2.4.4.1: Add a reordered outer-INR frame boundary lemma
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: This is a wrapper around an already-proved local theorem with the same mathematical conclusion. The only care is premise ordering and keeping the statement close to the live branch assumptions.
- Checkpoint: yes
- Carries progress/evidence from: E1274

#### Progress note
E1274 supplies the exact failed consumer goal and confirms `intcall_default_finally_inr_preserves_frame_from_caller_ctx` is available before the consumer theorem.

#### Summary
Introduce a local theorem for the outer-INR branch of `intcall_default_success_post_push_sound`. The lemma should conclude the exact frame triple for `fin_st`. It should be proved by applying `intcall_default_finally_inr_preserves_frame_from_caller_ctx`, not by unfolding `finally`. Its premise order should make the `finally ... = (INR y,fin_st)` equation and the live body IH easy to consume at the call site.

#### Statement
```sml
Theorem intcall_default_success_post_push_outer_inr_frame[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) /\
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
```

#### Approach
After `rpt gen_tac >> strip_tac`, apply `intcall_default_finally_inr_preserves_frame_from_caller_ctx` with the same variable order as its theorem statement. Discharge the generated conjunction using the assumptions from the boundary lemma; for `context_well_typed`/`functions_well_typed` under the pushed stack, use the already-used stack-irrelevance rewrites if they appear. Keep the proof short; this theorem must not inspect the internals of `finally`.

#### Not to try
Do not unfold `finally_def`, `bind_def`, or `eval_stmts` in this lemma. Do not add premises such as `well_typed_expr` or `expr_type`; they are irrelevant to frame restoration and would only make the consumer harder. Do not prove a more general continuation/safe-cast theorem here unless this exact wrapper still fails.

### C2.6.4.2.4.4.2: Outer-INR frame boundary repair
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The previous high risk is resolved by decomposing into a boundary lemma plus a mechanical consumer refactor.
- Progress transition: `refinement`
- Carries progress/evidence from: E1282

#### Progress note
E1282 is accepted as stuck evidence and reclassified into a concrete local repair plan.

#### Summary
Group for repairing the outer-INR frame proof interface. Prove the return-polymorphic boundary first, then replace the consumer's failed `_apply` call.

#### Argument
A return-polymorphic frame boundary is sufficient because the `NoneT` case delegates to the existing helper and the no-fallthrough case rules out normal success before using body-exception cleanup preservation.

#### Definition design
No definitions. One boundary theorem must match the live consumer assumptions exactly.

#### Code structure
All work remains in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.

### C2.6.4.2.4.4.2.1: Repair `intcall_default_success_post_push_sound` outer-INR frame restoration with a return-polymorphic boundary
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: All required ingredients already exist in the local source: the body IH is return-polymorphic, `intcall_finally_try_handle_inr_body_cleanup_cases` classifies the failing finally result, and `intcall_cleanup_after_body_preserves_caller_frame` restores the caller frame after cleanup. The only failed part was using a `NoneT`-specific convenience wrapper where the consumer has arbitrary `ret`; a local boundary lemma with the main theorem's premises should be a standard proof by the same case split as the existing `NoneT` helper.
- Checkpoint: yes
- Supersedes: C2.6.4.2.4.4.2.1.a, C2.6.4.2.4.4.2.1.b
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260525T153549Z_m58305_t001, TO_type_system_rewrite-20260525T153549Z_m58329_t001
- Invalidates prior progress/evidence: TO_type_system_rewrite-20260525T153549Z_m58320_t001, TO_type_system_rewrite-20260525T153549Z_m58338_t001

#### Progress note
Carries forward the solved INL return-exception/safe-cast work and the current focused residual from `m58329`: only the outer-INR frame triple remains. Invalidates the old split where `.a` supplied a separate boundary and `.b` consumed it, because decomposition pressure blocks beginning `.a` and the split encouraged a stale `NoneT`-only helper interface.

#### Summary
- Replace the over-decomposed local split by one beginable proof-refactor component.
- Add a local return-polymorphic outer-INR frame boundary for default internal calls.
- The boundary must consume `type_stmts env_body ret body = SOME env_after` and `(ret = NoneT \/ stmts_no_fallthrough body)`, not require `type_stmts env_body NoneT body = SOME env_after`.
- Use that boundary to close the remaining `finally ... = (INR y,fin_st)` residual in `intcall_default_success_post_push_sound`.
- Preserve the already-solved INL/safe-cast branch; do not rework it unless holbuild shows regression.

#### Description
Work only in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the local internal-call helper cluster and theorem `intcall_default_success_post_push_sound`. The source currently has a focused residual after the INL branch: assumptions include the body IH, `type_stmts env_body (expr_type (Call ...)) body = SOME env_after`, `stmts_no_fallthrough body`, pushed-scope consistency, and `finally ... = (INR y,fin_st)`, with goal `state_well_typed fin_st /\ env_consistent env cx fin_st /\ accounts_well_typed fin_st.accounts`. The repair is to introduce/use a boundary lemma whose statement matches this arbitrary-return/no-fallthrough context, then replace the failed `_apply`/`NoneT` consumption in the outer-INR residual.

#### Statement
Add/prove a local helper with this shape, using exact variable names/types adjusted to source conventions:

```sml
Theorem intcall_default_success_post_push_outer_inr_frame_ret[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after ret y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    env_consistent env cx args_st ==>
    state_well_typed args_st ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) ==>
    state_well_typed (lock_st with scopes := [call_env]) ==>
    context_well_typed cx ==>
    accounts_well_typed lock_st.accounts ==>
    functions_well_typed cx ==>
    env_body.type_defs = get_tenv cx ==>
    env_body.bare_globals = env.bare_globals ==>
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
```

Then close the remaining outer-INR branch of:

```sml
Theorem intcall_default_success_post_push_sound[local]: ...
```

#### Approach
Prove the new helper by copying the structure of `intcall_default_finally_inr_preserves_frame_from_caller_ctx`, but do not specialize body typing to `NoneT`. First classify the failing `finally` result with `intcall_finally_try_handle_inr_body_cleanup_cases`. In the normal-body-success cleanup case, split the `(ret = NoneT \/ stmts_no_fallthrough body)` premise: if `ret = NoneT`, use the body IH at `ret`; if `stmts_no_fallthrough body`, derive contradiction from `no_fallthrough_eval_no_success` for the observed `eval_stmts ... = (INL (),st_bdy)`. In the body-exception case, use the body IH at the actual `ret`, obtain `env_exn` and `env_extends env_body env_exn`, then feed `intcall_cleanup_after_body_preserves_caller_frame` with `env_exn` just as the existing `NoneT` helper does.

After the helper builds, the consumer branch in `intcall_default_success_post_push_sound` should be a short application: derive the local pushed preconditions from `intcall_live_pushed_body_preconditions` as already done, specialize the helper at `ret = expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)` (or use the existing `ret` variable if not rewritten by `gvs`), discharge static equalities and caller-context well-typedness using `context_well_typed_stk_irrelevant`/`functions_well_typed_stk_irrelevant`, and supply the `finally ... = (INR y,fin_st)` assumption. Keep the current selected branch style; the proof should not need broad unfolding of `finally` or monad definitions.

#### Not to try
Do not try to prove `type_stmts env_body NoneT body = SOME env_after` from `stmts_no_fallthrough body`; the previous failure shows no-fallthrough gives an evaluation contradiction for normal success, not a typing-ret equality. Do not append another duplicate selected `finally = INR` tail after QED residuals; repair the boundary and consume it once. Do not unfold `finally`, `try`, `handle_function`, `bind`, and all monadic definitions broadly in this theorem; it timed out and obscures the intended classifier-lemma proof. Do not disturb the already-solved INL return-exception/safe-cast branch unless holbuild reports a new regression.

### C2.6.4.2.5: IntCall actual/default/body wrapper proof layer
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Structural parent included only to satisfy dotted component validation. Its live wrapper child has been closed by E1327; residual verification is mechanical.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.6.4.2.5 plan, episode:E1327

#### Progress note
Validation parent only. No siblings under this parent are revised in this scoped update.

#### Summary
Wrapper-proof grouping parent for IntCall actual/default/body phases. The live wrapper branch under .6.4 is now audit-only. Sibling obligations are not changed here.

#### Approach
Only the new audit leaf is executable in this scoped update.

#### Not to try
Do not add tactical descendants for already-proved helper applications.

#### Argument
The wrapper layer decomposes the generated evaluator context into reusable local premises so the main mutual proof does not manually reconstruct every call-body invariant. The completed child proves the live/default-failure interface needed at this point.

#### Definition design
No definition changes. Boundary helpers should match consumer branches rather than forcing broad `AllCaseEqs()` cleanup.

#### Code structure
Keep all local wrapper lemmas in `vyperTypeStmtSoundnessScript.sml` near the IntCall proof.

### C2.6.4.2.5.1: Carry forward cleanup of the partial full-continuation draft
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already closed by E1286; no remaining executor work in the replacement subtree.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.6.4.2.5.1, E1286

#### Progress note
Prior cleanup remains valid and is retained so the replaced subtree preserves established progress.

#### Summary
Carry forward the completed cleanup that removed the earlier non-build-clean full-continuation draft. This component has no new work. It remains in the subtree only to preserve dependency history for later IntCall helpers.

#### Description
No edits required unless the executor discovers that E1291 reintroduced stale draft code; any such cleanup is owned by C2.6.4.2.5.3.

#### Approach
Treat as already discharged by E1286.

#### Not to try
Do not repeat this cleanup or broaden it to unrelated IntCall cases.

### C2.6.4.2.5.2: Carry forward packaged generated body IH after function push
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: Already proved by E1287 and explicitly useful in E1291; its conclusion is the right premise shape for the direct success helper.
- Dependencies: C2.6.4.2.5.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.6.4.2.5.2, E1287

#### Progress note
The stuck episode confirms this helper remains useful; only its downstream consumer interface changes.

#### Summary
Carry forward `intcall_generated_body_post_push_ih`. It packages the generated evaluator IH into the concrete post-push body premise used by successful IntCall body/tail soundness. No new proof work is required here.

#### Statement
Existing local theorem in `vyperTypeStmtSoundnessScript.sml`:

```sml
Theorem intcall_generated_body_post_push_ih[local]:
  ... ==>
  !env1 ret_ty1 env2 st0 res0 st0'.
    type_stmts env1 ret_ty1 body0 = SOME env2 /\
    env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
    context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
    functions_well_typed cx0 /\ eval_stmts cx0 body0 st0 = (res0,st0') ==>
    state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
    no_type_error_result res0 /\
    case res0 of
    | INL v => env_consistent env2 cx0 st0'
    | INR exn => ?env_exn. env_extends env1 env_exn /\
        env_consistent env_exn cx0 st0' /\
        return_exception_typed env_exn ret_ty1 exn
```

#### Approach
Use this theorem only to cut a named body-IH fact in the success-case helper. Its conclusion should not appear as a large unsolved goal in the final continuation theorem.

#### Not to try
Do not inline the older `intcall_generated_body_ih_live_consumer_premise` in downstream proofs.

### C2.6.4.2.5.3: Stabilize the helper cluster and stop using the over-broad generalized wrapper as the continuation boundary
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: The required edit is organizational: keep proved/useful local helpers, but remove or bypass the partial continuation proof shape that E1291 showed is brittle and non-build-clean.
- Dependencies: C2.6.4.2.5.2
- Supersedes: old C2.6.4.2.5.3
- Progress transition: `replacement`
- Carries progress/evidence from: E1291, TO_type_system_rewrite-20260525T153549Z_m58580_t001
- Invalidates prior progress/evidence: E1291 continuation proof attempt, direct application of `intcall_successful_defaults_lock_success_sound_general` in `intcall_successful_defaults_continuation_sound_general`

#### Progress note
E1291 showed that a one-line tail fix made `intcall_successful_defaults_lock_success_sound_general` pass, but the continuation proof still timed out. This component preserves the useful direct/body-IH work and removes the failed continuation application as the active proof boundary.

#### Summary
Edit `vyperTypeStmtSoundnessScript.sml` around the IntCall helper cluster. Retain `intcall_successful_defaults_lock_success_sound_from_body_ih` and the carried-forward `intcall_generated_body_post_push_ih`. Do not let the theorem `intcall_successful_defaults_continuation_sound_general` depend on a long direct application of `intcall_successful_defaults_lock_success_sound_general`. Prepare the source for a new lock-success branch helper immediately before the continuation theorem.

#### Description
If `intcall_successful_defaults_lock_success_sound_general` is already build-clean after the E1291 tail-equality fix, it may remain as a local helper, but it is not the consumer boundary for the continuation theorem. If it is still partial or only used by the failed continuation proof, delete it rather than repair it further. The stable boundary to rely on is the direct helper that assumes the concrete body IH.

#### Approach
Inspect the current source around lines 14685-15120. Ensure the direct helper is before the new branch theorem and that the continuation theorem is not left with the E1291 timeout script. This component may leave the theory temporarily non-build-clean until C2.6.4.2.5.4/C2.6.4.2.5.5 fill the replacement proof.

#### Not to try
Do not spend this component proving new semantic facts. Do not add another generalized theorem with all evaluator phase facts unless its conclusion exactly matches a downstream branch goal.

### C2.6.4.2.5.4: Prove a consumer-shaped lock-success case for successful-defaults continuation soundness
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: All semantic ingredients are already proved; the new theorem changes the proof interface so the final continuation theorem consumes a branch-shaped result instead of replaying the generated-IH bundle.
- Dependencies: C2.6.4.2.5.3
- Checkpoint: yes
- Supersedes: old C2.6.4.2.5.3
- Progress transition: `reclassified`
- Carries progress/evidence from: C2.6.4.2.5.2, E1287, E1291
- Invalidates prior progress/evidence: E1291 direct continuation-success branch attempt

#### Progress note
This is the substantive replacement for the stuck portion of old C2.6.4.2.5.3. The old evidence carries forward by identifying the direct body-IH helper as useful and the final-theorem premise plumbing as the failure mode.

#### Summary
Add a local theorem immediately before `intcall_successful_defaults_continuation_sound_general`. Its hypotheses should be the same live assumptions as the continuation theorem, plus the success-branch fact `lock_res = INL ()` (or the equivalent branch after `Cases_on lock_res; Cases_on x`). Its conclusion should be exactly the final state/env/account/no-TypeError/result-typed conclusion of the continuation theorem. Prove it by deriving the concrete body IH with `intcall_generated_body_post_push_ih`, simplifying the lock-success case equation, and applying `intcall_successful_defaults_lock_success_sound_from_body_ih`.

#### Statement
Suggested local theorem shape; copy the full quantifier/hypothesis block from `intcall_successful_defaults_continuation_sound_general` to avoid variable/order drift:

```sml
Theorem intcall_successful_defaults_continuation_lock_success_case[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_res lock_st.
    (* same generated-IH premise and phase/static/runtime hypotheses as
       intcall_successful_defaults_continuation_sound_general *) /\
    lock_res = INL () ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
```

The copied hypotheses must include the continuation theorem's case expression:

```sml
(case lock_res of
 | INL u => (do rv <- finally ...; crv <- lift_option_type ...; return (Value crv) od)
              (lock_st with scopes := [call_env])
 | INR e => (INR e,lock_st)) = (res,st')
```

Under `lock_res = INL ()`, this simplifies to the tail equality expected by the direct success helper.

#### Approach
Start with `rpt gen_tac >> strip_tac`, split/carry assumptions, and rewrite `lock_res = INL ()` so the case-expression assumption becomes the concrete post-lock tail equality. Cut the body IH once using `intcall_generated_body_post_push_ih`; keep it as a named assumption. Then apply `intcall_successful_defaults_lock_success_sound_from_body_ih`, discharging premises in small groups: generated body IH, expression/type/static hypotheses, runtime well-typedness hypotheses, `env_body.current_src = src_id_opt` rewrite for immutables, scope consistency, lock equality, and tail equality.

#### Not to try
Do not prove this theorem by first proving another generalized all-phase wrapper and then applying it with a long `Q.SPECL` list. Do not leave the generated-IH quantified formula as an unsolved subgoal after entering the final continuation theorem. Avoid a single huge tactic fragment; split the body-IH cut and the direct-helper application into separate `by` facts if holbuild's 2.5s tactic timeout appears.

### C2.6.4.2.5.5: Prove full successful-defaults continuation soundness by lock-result case split
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: After the success-case theorem, the continuation proof is a straightforward case split: success delegates to C2.6.4.2.5.4 and failure uses the already-existing lock frame lemma.
- Dependencies: C2.6.4.2.5.4
- Checkpoint: yes
- Supersedes: old C2.6.4.2.5.3
- Progress transition: `reclassified`
- Carries progress/evidence from: E1291, C2.6.4.2.5.4
- Invalidates prior progress/evidence: old monolithic proof of `intcall_successful_defaults_continuation_sound_general`

#### Progress note
This closes the old C2.6.4.2.5.3 obligation through a lower-risk interface: the final theorem no longer performs generated-IH/body/tail premise plumbing itself.

#### Summary
Replace the body of `intcall_successful_defaults_continuation_sound_general`. Keep the two small preliminary `lift_option_type` facts if still useful. Then case-split on `lock_res`: in the `INL ()` branch, simplify the case expression and invoke `intcall_successful_defaults_continuation_lock_success_case`; in the `INR e` branch, reuse the existing `intcall_lock_attempt_sound_frame` argument. The theorem should build without exposing a >4KB generated-IH subgoal.

#### Statement
Existing theorem to prove build-clean:

```sml
Theorem intcall_successful_defaults_continuation_sound_general[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_res lock_st.
    ... ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
```

#### Approach
Use `Cases_on lock_res`; in the `INL x` branch, `Cases_on x` to get unit success, simplify the case equation, and apply the success-case theorem from C2.6.4.2.5.4 with live assumptions. In the `INR y` branch, simplify the case equation to `res = INR y`/`st'=lock_st` and apply `intcall_lock_attempt_sound_frame` as in the existing proof. Verify with `holbuild build vyperTypeStmtSoundnessTheory` if this theorem is the next failure point.

#### Not to try
Do not apply `intcall_successful_defaults_lock_success_sound_general` directly from this theorem. Do not derive the body IH here. Do not use a broad `rpt conj_tac` over all continuation hypotheses.

### C2.6.4.2.5.6: Live IntCall return/default-failure wrapper layer
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Structural parent included only to satisfy dotted component validation. The direct child C2.6.4.2.5.6.4 is being refined from blocked to audit-only after all semantic leaves were proved/reviewed.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.6.4.2.5.6 plan, episode:E1327

#### Progress note
Validation parent only. No sibling under .6 is revised here.

#### Summary
Live IntCall return/default-failure grouping parent. The hard wrapper proof under .6.4 is complete. This update authorizes final local verification only.

#### Approach
Descend to C2.6.4.2.5.6.4.4 for audit.

#### Not to try
Do not repair future premise mismatches by growing long theorem-plumbing chains without escalation.

#### Argument
The successful proof path splits default-failure from success-tail reasoning early, then uses generated-IH consumer premises in the success branch. This avoids the previous direct no-TypeError-result blocker for an exception/error tail.

#### Definition design
The interface is now stable: use branch-tail helpers and generated-IH consumer premises; do not unfold evaluator internals repeatedly in consumers.

#### Code structure
All changes are local to the IntCall helper/proof region in `vyperTypeStmtSoundnessScript.sml`.

### C2.6.4.2.5.6.1: Retain the local default-failure tail helper
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: E1300 evidence indicates `intcall_default_failure_tail` was already proved once by unfolding `no_type_error_result_def`; the remaining failure was in its consumer, not in this helper.
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260525T153549Z_m58796_t001, E1300

#### Progress note
Carry forward the proved tail-helper idea. If current source already contains the helper, keep it; otherwise restore it with the same statement shape.

#### Summary
- Keep or restore `intcall_default_failure_tail[local]` before the main wrapper.
- The helper should prove the final IntCall preservation package from frame facts and the fact that `INR` results are not TypeErrors.
- Its proof should be tiny: split conjunctions and unfold `no_type_error_result_def`/sum case only as needed.
- This helper is not the place to reason about generated IHs or defaults evaluation.

#### Statement
Keep the current local theorem if present. Equivalent intended shape:
```sml
Theorem intcall_default_failure_tail[local]:
  !env cx dflt_st y loc src_id_opt fn es extra res st'.
    state_well_typed dflt_st /\
    env_consistent env cx dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    (INR y,dflt_st) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
```
If the current source has the same conclusion with extra harmless premises, do not churn it.

#### Approach
Use only conjunction splitting, pair equality/substitution, `sum_case_def`, and `no_type_error_result_def`. The successful-result typing arm is unreachable after the `INR` substitution.

#### Not to try
Do not invoke the defaults package lemma or generated IHs here. Do not use `metis_tac[]`; prior evidence showed the extensional definition of `no_type_error_result` needs explicit unfolding.

### C2.6.4.2.5.6.2: Add a consumer-shaped default-failure branch helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: This is a direct wrapper around the frame facts produced by the defaults package plus the already-proved tail helper. It avoids applying the tail helper after destructive case rewrites in the giant theorem.
- Dependencies: C2.6.4.2.5.6.1
- Carries progress/evidence from: E1300

#### Progress note
New helper introduced because E1300 showed direct use of `intcall_default_failure_tail` inside the monolithic proof remains brittle.

#### Summary
- Prove a local helper for the `dflt_res = INR e` branch of the authoritative wrapper.
- The helper should consume stable frame facts for `dflt_st` before any case-expression normalization.
- Its conclusion is the same final preservation package for `(res,st')`.
- The proof should rewrite the outer default-failure computation to `(INR e,dflt_st)` and call `intcall_default_failure_tail`.

#### Statement
Use a local theorem immediately before the main wrapper, preferably with this simple consumer shape:
```sml
Theorem intcall_actual_args_success_default_failure_branch[local]:
  !cx env loc res st' src_id_opt fn es extra y dflt_st.
    state_well_typed dflt_st /\
    env_consistent env cx dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    (INR y,dflt_st) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
```
If the main theorem applies it before simplifying the outer `case dflt_res`, use the equivalent premise `(case INR y of INL _ => continuation | INR e => (INR e,dflt_st)) = (res,st')`; the proof should immediately rewrite this to the pair equality above.

#### Approach
State the helper so the main theorem can call it immediately in the `dflt_res = INR y` branch with the frame facts from the defaults package. Normalize only `sum_case_def` and `PAIR_EQ`, then pass the resulting pair equality and frame facts to `intcall_default_failure_tail`; prove any remaining `no_type_error_result (INR y)` side goal by `rw[no_type_error_result_def]`.

#### Not to try
Do not discharge this branch by selecting assumptions after the main theorem has substituted both `res` and `st'` in a massive context. Do not include generated-IH premises in this helper; if they appear in the goal, the helper is being applied too late or its statement is too weak.

### C2.6.4.2.5.6.3: Add a consumer-shaped default-success continuation helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: The success branch is already mathematically covered by `intcall_successful_defaults_continuation_sound_general`; the risk is only matching its many premises without replaying generated-IH plumbing in the final wrapper. A wrapper helper with the generated IHs and package facts as stable leading premises is standard.
- Carries progress/evidence from: E1300

#### Progress note
New helper introduced to isolate the application of `intcall_successful_defaults_continuation_sound_general` from the final wrapper's huge case-split context.

#### Summary
- Prove a local helper for the `dflt_res = INL dflt_vs` branch.
- The helper wraps `intcall_successful_defaults_continuation_sound_general` and has the same final preservation conclusion.
- Include the body generated-IH premise and all package facts required by the continuation theorem as explicit leading premises.
- The proof should be a single application of the continuation theorem with targeted premise discharge, not another monolithic semantic proof.

#### Statement
Introduce a local theorem whose conclusion is the same final preservation package as the main wrapper and whose premises are exactly the stable facts used at the current call site for the `INL dflt_vs` branch:
```sml
Theorem intcall_actual_args_success_default_success_branch[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_res lock_st.
    (* generated body-IH premise from the main theorem *) /\
    (* evaluator prefix facts and package facts required by
       intcall_successful_defaults_continuation_sound_general *) /\
    (* final continuation computation for the INL-defaults branch equals (res,st') *) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
```
Do not invent a weaker theorem: copy the exact premises required by `intcall_successful_defaults_continuation_sound_general` plus the one generated body-IH premise from the current source, using the current theorem's variable names.

#### Approach
Apply `intcall_successful_defaults_continuation_sound_general` directly. Discharge its first premise using the generated body-IH assumption by exact matching before any `rpt conj_tac`; discharge the rest using explicitly named package facts. If `env_body.current_src = src_id_opt` is used by the continuation theorem with `env_body.current_src`, rewrite once with that equality before matching the IH, rather than letting broad simplification rewrite the whole goal.

#### Not to try
Do not make the final authoritative theorem replay the continuation theorem's generated-IH premises. Do not use `rpt conj_tac >> first_assum ACCEPT_TAC` over the entire premise list; split the generated-IH premise(s) first and use exact assumptions, then handle ordinary scalar/package facts.

### C2.6.4.2.5.6.4: Close the live IntCall wrapper verification checkpoint
- Kind: `integration_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: All semantic proof obligations in this IntCall wrapper subtree were already proved and reviewed, with `vyperTypeStmtSoundnessTheory` building in E1327. The only remaining obligation is mechanical verification of the current working tree against that stable checkpoint and repository hygiene; no new theorem or tactic design is required.
- Checkpoint: yes
- Supersedes: C2.6.4.2.5.6.4.1, C2.6.4.2.5.6.4.2, C2.6.4.2.5.6.4.3, C2.6.4.2.5.6.4.4
- Progress transition: `reclassified`
- Carries progress/evidence from: C2.6.4.2.5.6.4.1, C2.6.4.2.5.6.4.2, C2.6.4.2.5.6.4.3, episode:E1306, episode:E1307, episode:E1327, tool_output:TO_type_system_rewrite-20260525T153549Z_m59889_t001
- Invalidates prior progress/evidence: C2.6.4.2.5.6.4.4

#### Progress note
The previous durable proof leaves under this subtree are reclassified as completed evidence carried by this single checkpoint component. The old audit child C2.6.4.2.5.6.4.4 is invalidated only as a PLAN artifact because the harness flagged it as over-decomposition; its intended audit work is now the direct work of C2.6.4.2.5.6.4.

#### Summary
- This leaf replaces the over-decomposed IntCall wrapper verification subtree with one beginable checkpoint.
- Carry forward the proved NoneT generated-IH consumer, live generated-IH consumer, and default-failure-tail wrapper refactor from E1306/E1307/E1327.
- Run a focused source/build audit to confirm `vyperTypeStmtSoundnessTheory` still builds in the current working tree.
- Inspect `git status`/relevant diffs before any checkpointing because the repo contains unrelated tracked diffs and untracked scratch files.
- If the focused build regresses inside the same IntCall tail, stop and escalate for a real compatibility-helper redesign; do not add more tactical audit children.

#### Description
This component is intentionally a leaf even though it carries the old subtree's completed semantic evidence. The old plan decomposed the last step into an audit child, but that child was not durable mathematical work and triggered decomposition pressure. The executor should perform only a focused verification checkpoint: inspect the working tree, run the authorized build, and report/close this component if the build and diff hygiene match the reviewed E1327 state.

#### Statement
No new HOL theorem statement. Checkpoint obligation:

```sh
holbuild build vyperTypeStmtSoundnessTheory
```

must succeed in the current working tree, and the executor must verify that any staged/checkpointed changes are limited to task-owned IntCall wrapper proof edits in `semantics/prop/vyperTypeStmtSoundnessScript.sml` plus strictly necessary generated/build artifacts if the project convention requires them.

#### Approach
First inspect `git status` and the relevant diff around `semantics/prop/vyperTypeStmtSoundnessScript.sml`, especially the IntCall helper/proof cluster around the E1327 edits. Then run `holbuild build vyperTypeStmtSoundnessTheory` with the normal timeout. If it succeeds, close this checkpoint and, only if committing/checkpointing is requested by the workflow, stage narrowly selected relevant files rather than using `git add -A`.

#### Not to try
Do not begin by editing the accepted IntCall proof for style or by adding another child component. Do not reopen the explicit post-helper `CONJ_TAC` tail unless the build actually regresses. Do not use `git add -A`, and do not stage untracked `test_*` scratch files. If a new IntCall premise-tail failure appears, do not continue line-by-line `qpat_assum`/`FIRST_ASSUM` repairs; escalate for a local compatibility-helper interface that packages the whole downstream tail.

### C2.6.4.2.5.7: Build-audit the IntCall successful-defaults helper cluster
- Kind: `build_audit`
- Risk: 1
- Work priority: 50
- Work units: 1
- Rationale: After replacing a stuck local proof interface, a focused build is necessary and mechanical.
- Dependencies: C2.6.4.2.5.6
- Checkpoint: yes
- Supersedes: C2.6.4.2.5.5@old
- Progress transition: `reclassified`
- Carries progress/evidence from: C2.6.4.2.5.5@old plan

#### Progress note
Renumbered from the old build-audit component after inserting the success-case repair components.

#### Summary
Run `holbuild build vyperTypeStmtSoundnessTheory`. Confirm the helper cluster around the IntCall actual/default path is build-clean and that no new CHEATs or suspended fragments were introduced in this cluster. If the next failure is outside this subtree, close this checkpoint with the exact next theorem/location for downstream planning.

#### Approach
Use the task-required `holbuild` path, not direct HOL. Inspect warnings as well as errors; this task ultimately requires zero reachable CHEAT warnings. Record the next failing theorem if the build advances beyond the helper cluster.

#### Not to try
Do not treat a failed focused build as success because an earlier theorem compiled. Do not broaden into assignment/builtin/call sibling work from this audit component.

### C2.6.4.3: Assemble a full `IntCall` expression-soundness helper from generated IHs
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: This helper is a consumer-shaped wrapper over the phase lemmas. Its proof follows the already-validated evaluator split from `intcall_expr_no_type_error_from_generated_ih`, with stronger conclusions delegated to C2.6.4.1 and C2.6.4.2.
- Dependencies: C2.6.4.1, C2.6.4.2
- Checkpoint: yes
- Supersedes: intcall_expr_no_type_error_from_generated_ih
- Carries progress/evidence from: E1236, E1237, E1238

#### Progress note
Carries forward the expanded evaluator proof and repaired IH selectors from prior episodes, but supersedes the no-TypeError-only helper as the boundary to be used by the resume.

#### Summary
- Prove a local theorem whose conclusion exactly matches the first conjunct of the live mutual `Expr_Call_IntCall` goal.
- Hypotheses should be the same three generated IH assumptions already selected in the resume, plus ordinary well-typed/evaluation/context assumptions.
- Prefix error and actual-argument failure branches are solved directly from state-unchanged facts or the actual generated IH.
- Actual-argument success delegates defaults to C2.6.4.1 and successful continuation to C2.6.4.2.

#### Statement
Add local theorem `intcall_expr_sound_from_generated_ih[local]` before the resume:

```sml
!cx env st res st' loc src_id_opt fn es extra.
  <actual-args generated-IH assumption> /\
  <defaults generated-IH assumption, including get_scopes/set_scopes binders> /\
  <body generated-IH assumption> /\
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx (Call loc (IntCall (src_id_opt,fn)) es extra) st = (res,st') /\
  well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
  | INR _ => T
```

#### Approach
Copy the top-level case structure from `intcall_expr_no_type_error_from_generated_ih`: strip `well_typed_expr`, name the three generated IHs, unfold `evaluate_def`, and handle prefix failures with the same check/lift/type-check state lemmas. On actual-argument failure, use the actual IH to obtain preservation and no-TypeError, with result-typing trivial because result is `INR`. On actual-argument success, derive callable body typing as in E1238, call C2.6.4.1 for defaults; if defaults fail, use its all-result frame package, and if defaults succeed, call C2.6.4.2.

#### Not to try
Do not make this theorem conclude only `no_type_error_result res`; that is the E1238 mismatch. Do not require callers to manually pass `env_body`, `ret_tv`, `env_after`, `dflt_res`, or `dflt_st` unless unavoidable; the final resume should only pass generated IHs and live assumptions. Avoid a massive `Q.SPECL` in the resume by hiding evaluator intermediates inside this helper.

### C2.6.4.4: Integrate the full helper into `eval_all_type_sound_mutual[Expr_Call_IntCall]`
- Kind: `proof_integration`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: Once C2.6.4.3 exists, the resume is mechanical: split the two conjuncts, select generated IHs, apply the full helper to the first conjunct, and use the place-expression impossibility lemma for the second conjunct.
- Dependencies: C2.6.4.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E1236, E1237, E1238

#### Progress note
Keeps the successful split and `type_place_expr_Call_IntCall_NONE` from prior episodes. Invalidates only the attempted `MATCH_MP_TAC` application of the no-TypeError-only helper, not surrounding integration work.

#### Summary
- Replace the failing lines around 13759-13763 with an application of `intcall_expr_sound_from_generated_ih`.
- Keep `reverse conj_tac`: second conjunct is solved by contradiction with `type_place_expr_Call_IntCall_NONE`.
- The first conjunct should not unfold the entire continuation after the full helper is available.
- Run focused `holbuild build vyperTypeStmtSoundnessTheory`; expected next failures, if any, should be later branches such as `Expr_Call_ExtCall`.

#### Statement
Close the existing source obligation:

```sml
Resume eval_all_type_sound_mutual[Expr_Call_IntCall]:
  ...
QED
```

The first conjunct must close through `intcall_expr_sound_from_generated_ih`; the second conjunct must close through `type_place_expr_Call_IntCall_NONE`.

#### Approach
Retain the repaired generated-IH selection patterns from E1238. For the first conjunct, use `MATCH_MP_TAC`/`irule` on `intcall_expr_sound_from_generated_ih` and discharge generated-IH premises by the named `actual_ih`, `default_ih`, and `body_ih`; ordinary assumptions should be solved by `first_assum ACCEPT_TAC` and already-unfolded well-typed facts. For the second conjunct, keep the current contradiction from `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` and `simp[type_place_expr_Call_IntCall_NONE]`.

#### Not to try
Do not reintroduce the long `Q.SPECL` application of `intcall_actual_args_success_no_type_error_from_generated_ih_general`. Do not leave preservation/result-typing subgoals to a broad `rw` tail. If applying the full helper still needs many explicit intermediate arguments, stop and adjust C2.6.4.3's statement to hide those intermediates.

### C2.7: Close remaining non-internal call-target expression branches
- Kind: `proof`
- Risk: 2
- Work priority: 80
- Work units: 5
- Rationale: IntCall is now proved (E1332). ExtCall/RawCallTarget cheats are the remaining statement-soundness expression branches. Tooling blocker (--strict-parse) has been resolved; holbuild works without that option.
- Dependencies: C2.6.4
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
The --strict-parse tooling blocker is resolved. Build passes with 3 remaining cheats: Expr_Call_ExtCall, Expr_Call_RawCallTarget in vyperTypeStmtSoundnessScript.sml and raw_call_return_type_well_formed in vyperTypeBuiltinsScript.sml. IntCall is fully proved.

#### Summary
- Prove Expr_Call_ExtCall resume in vyperTypeStmtSoundnessScript.sml.
- Prove Expr_Call_RawCallTarget resume in vyperTypeStmtSoundnessScript.sml.
- Both should use a standalone local helper theorem outside the Resume, then the Resume just applies it.

#### Approach
For **ExtCall**, write `extcall_expr_sound[local]` before the Resume:
1. Take IHs for eval_exprs and eval_expr (THE drv) as explicit premises.
2. Unfold `well_typed_expr_def` and `evaluate_def` Once.
3. Case-split on `eval_exprs cx es st`; use IH for success; error case is trivial (all RuntimeErrors, not TypeErrors).
4. Case-split on `is_static`; use `extcall_static_args_runtime_typed_dest` or `extcall_nonstatic_args_runtime_typed_dest`.
5. Step-by-step simplify monadic operations (check, lift_option_type, lift_option, get_accounts, get_transient_storage) — unfold 1-2 defs at a time, case-split results.
6. For run_ext_call: case-split, use `run_ext_call_accounts_well_typed`.
7. After check success + update_accounts/update_transient: bridge to `extcall_return_tail_sound`.
   - Key bridging issue: the evaluator produces `(\\(success,returnData,accounts',tStorage'). ...) result` (lambda applied to result tuple) which must be simplified to match `extcall_return_tail_sound`'s expected shape.
   - Use `simp[update_accounts_def, update_transient_def, return_def, PAIR_EQ]` then further simplification.
   - Derive `evaluate_type env.type_defs ret_type2 = SOME ret_tv` from `well_formed_type_def` + `IS_SOME_EXISTS`.
   - Use `runtime_consistent_def` and `update_accounts_transient_runtime_consistent` for the state after account/transient update.
   - The driver IH for `eval_expr cx (THE drv)` is in the third premise; pass it through when `drv = SOME e`.
8. Place-expression second conjunct is vacuously true (`type_place_expr ... Call (ExtCall ...) ... = NONE`).

For **RawCallTarget**, follow the same pattern with the RawCallTarget evaluator clause (simpler: no driver, fewer bound operations).

#### Not to try
- Do not unfold ALL monadic definitions at once with `simp_tac(srw_ss())[Once evaluate_def, bind_def, ...]` — causes timeout/explosion.
- Do not use `<| ... |>` record update syntax inside backtick quotations in the Resume context — causes parse errors due to `markerLib.resume` wrapper limitations.
- Do not try to prove ExtCall inside the Resume inline; use a standalone helper theorem.
- Do not inline `run_ext_call`/ABI/rollback internals in the Resume.

### C2.8: Focused statement-soundness build and C2 cheat audit
- Kind: `build_audit`
- Risk: 1
- Work priority: 90
- Work units: 1
- Rationale: The audit remains valid and should run after C2.6 and C2.7, not before the active repair path.
- Dependencies: C2.7
- Progress transition: `refinement`

#### Progress note
Priority/dependency refined so the audit remains final within C2 after the proof leaves complete.

#### Summary
- Final C2-focused build/cheat audit.
- Unchanged obligation, rescheduled after the active IntCall and call-target proof leaves.

### C3: Update-binop and assignment-subscript runtime-typed path
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The inherited cheats form a localized dependency chain from binop no-TypeError through assignment operation leaf and recursive subscript no-TypeError/preservation. They must be closed before any consumers can count as CHEAT-free, and C4 builtin facts may depend on the binop boundary.
- Required for completion: yes
- Dependencies: C1
- Progress transition: `refinement`
- Carries progress/evidence from: old C3

#### Progress note
C3 is moved before C4/C2 remaining consumers. It owns the inherited update-binop path listed in the TASK and prevents hidden CHEAT dependencies from leaking into statement/builtin proofs.

#### Summary
- Prove the inherited update-binop path without cheats.
- Start with generic binop no-TypeError, then operation leaf soundness, then recursive subscript no-TypeError/preservation.
- C4 builtin boundaries depend on the binop part when they reason about binary operations.
- C2 assignment/Pop consumers may rely on these theorems only after C3 closes.

#### Description
This component is scheduled before C4.2 and before remaining C2 consumers because otherwise theorem proofs could build while still depending on CHEATed update/binop facts.

#### Statement
Close the current source-authoritative inherited path:
```sml
well_typed_binop_no_type_error
well_typed_update_binop_no_type_error
assign_subscripts_update_leaf_no_type_error
assign_operation_runtime_typed_leaf_no_type_error
assign_subscripts_no_type_error_runtime_typed
assign_subscripts_preserves_type_runtime_typed
```

#### Approach
Prove in dependency order: binop no-TypeError first, update-binop as a corollary, operation leaf no-TypeError, then recursive subscript no-TypeError and preservation by the existing recursion induction. Derive compatibility theorem names after any stronger joint lemma so downstream source need not change broadly.

#### Not to try
Do not let C2/C4 prove around these cheats. Do not split no-TypeError and preservation into independent recursive inductions if the current helper already carries both runtime typing and preservation information.

#### Argument
The chain is structural. A well-typed binary operation on typed operands never reaches the `TypeError` fallback branch of `evaluate_binop`; arithmetic failures are runtime errors or successful bounded values. Assignment operation leaf soundness then splits on `AssignOp`, `UpdateOp`, `AppendOp`, and `PopOp`: update uses the binop theorem, append/pop use array dynamic/fixed shape and existing value typing, and plain assignment uses the provided assigned value typing. Recursive `assign_subscripts` soundness follows the subscript list/path recursion, with the leaf theorem applied after the target path has reduced to the final leaf type.

#### Definition design
The boundary theorems should match existing current-source names in `vyperTypeStatePreservationScript.sml`: `well_typed_binop_no_type_error`, `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`. If existing statements are underspecified but not frozen, strengthen a joint helper and derive compatibility corollaries with these names. Failure signs are large consumers unfolding `evaluate_binop_def` or `assign_subscripts_def` outside this layer.

#### Code structure
Keep binop-specific facts in `vyperTypeBuiltinsScript.sml` if the theorem currently lives there, and assignment-subscript recursion facts in `vyperTypeStatePreservationScript.sml`. Do not move statement-level assignment cases into this component; C2 only consumes the resulting boundary lemmas.

### C3.1: Close binop no-TypeError boundary lemmas
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: Finite case analysis over binop/type/value constructors is already supported by many local per-operator no-TypeError helpers in `vyperTypeBuiltinsScript.sml`. The main work is completing the generic theorem without cheat.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C3.1

#### Progress note
Moved earlier so C4 builtin boundaries do not depend on cheated binop facts.

#### Summary
- Replace the cheat for `well_typed_binop_no_type_error` and any direct binop no-TypeError scaffold it depends on.
- Use existing per-operator helper lemmas for concrete well-typed values.
- Export a theorem matching update-binop and builtin consumers.
- Checkpoint because many downstream leaves depend on this boundary.

#### Statement
Current source theorem, expected name:
```sml
Theorem well_typed_binop_no_type_error:
  ...
Proof
  ...
QED
```
and any immediate `well_typed_update_binop_no_type_error` corollary if it is in the same source region.

#### Approach
Unfold the well-typed binop predicate enough to identify the operator/type class and operand value constructors, then apply the local `binop_no_type_error_*` helpers rather than simplifying all of `evaluate_binop_def`. For success-typing side facts use existing binop success typing lemmas if present; otherwise keep the goal to no-TypeError only and split constructors locally.

#### Not to try
Do not use a single enormous `gvs[evaluate_binop_def, AllCaseEqs()]` over all operators if it causes case explosion. Do not prove arithmetic bounds in consumers; keep them here or in existing value/builtin helper layers.

### C3.2: Close assignment operation leaf no-TypeError
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: After C3.1, assignment operation leaves reduce by finite operation cases: update uses binop no-TypeError, append/pop use array operation facts, and plain assignment uses value typing.
- Dependencies: C3.1
- Progress transition: `refinement`
- Carries progress/evidence from: old C3.2

#### Progress note
C3.2 remains the strict prerequisite for recursive subscript closure.

#### Summary
- Prove `assign_subscripts_update_leaf_no_type_error` and `assign_operation_runtime_typed_leaf_no_type_error` without cheats.
- Consume C3.1 for update operations.
- Keep operation-shape assumptions explicit.
- Do not reason about recursive subscript traversal here.

#### Statement
Current source theorem names:
```sml
assign_subscripts_update_leaf_no_type_error
assign_operation_runtime_typed_leaf_no_type_error
```

#### Approach
Case split on the assignment operation and, for update, apply `well_typed_update_binop_no_type_error`. For append/pop, use the strengthened operation runtime typing (`PopOp` requires dynamic array) and existing array operation definitions to rule out `TypeError`; runtime errors are allowed.

#### Not to try
Do not fold recursive subscript preservation into this leaf. Do not drop the strengthened `assign_operation_runtime_typed` dynamic-array precondition for `PopOp`.

### C3.3: Close recursive assignment-subscript no-TypeError and preservation
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: The recursive helper follows the `assign_subscripts` recursion over the target path/subscripts and consumes the leaf operation theorem from C3.2.
- Dependencies: C3.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C3.3

#### Progress note
Checkpoint because C1/C2 final CHEAT-freedom depends on these recursive helpers no longer carrying cheats.

#### Summary
- Prove `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed` without cheats.
- Use recursion-matching induction over `assign_subscripts`.
- Leaf case consumes C3.2; recursive cases use target-path typing/leaf-type bridge lemmas.
- Preserve compatibility theorem names for existing callers.

#### Statement
Current source theorem names:
```sml
assign_subscripts_no_type_error_runtime_typed
assign_subscripts_preserves_type_runtime_typed
```

#### Approach
Use the function induction principle for `assign_subscripts` or structural induction on the subscript/path list, whichever matches the current definition. In each recursive branch, invert the relevant `target_path_type`/`place_leaf_typed` premise to obtain the sub-leaf type and apply the IH; in the base branch use C3.2.

#### Not to try
Do not reprove top-level storage/hashmap assignment branch facts here. Do not unfold callers like `assign_target`; this component is only about subscript recursion.

### C4: ABI/builtin prerequisite soundness stack (structural ancestor)
- Kind: `structural_context`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Carry-forward ancestor included only to satisfy dotted-component validation; this update changes no C4 siblings and the max risk of the edited C4.4.5 subtree is 2.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4, E0781

#### Progress note
No strategic change is made at C4 scope. The only substantive update is within descendant C4.4.5.

#### Summary
- Structural ancestor for ABI/builtin prerequisite obligations.
- Included only so the C4.4.5 dotted subtree validates.
- No C4 siblings are added, removed, reordered, or redesigned by this update.

#### Approach
Proceed only into the C4.4.5 subtree for executable work.

#### Not to try
Do not treat this structural parent as authorization to replan C4 siblings.

#### Argument
This ancestor carries the existing ABI/builtin prerequisite context. The current update does not change the C4-level argument; it only refines the local ABI encoding length-bound proof in C4.4.5.

#### Definition design
No C4-level definition design changes are made. New definitions introduced by this update are local to `vyperTypeABIScript.sml` under C4.4.5.

#### Code structure
No C4-level file organization changes are made. All executable edits from this update belong to `semantics/prop/vyperTypeABIScript.sml` in the C4.4.5 region.

### C4.1: Carry forward closed reachable static builtin-typing suspended cases
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0735 accepted this leaf as proved, and no current C4.4/C4.5 repair changes its statements or definitions.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.1, E0735

#### Progress note
Preserved as completed evidence under the C4 scheduling rebase.

#### Summary
- Static builtin-typing suspended cases are already closed or audited as unreachable.
- No executor work remains here.
- Later C4 leaves may rely on the generic static builtin interface being stable.

#### Statement
Already-proved reachable suspended cases in `vyperBuiltinTypingScript.sml` / builtin static typing support required by the fresh stack.

#### Approach
No action. If a future build reports a regression in this area, escalate with the exact theorem and dependency path.

#### Not to try
Do not reopen the large suspended static-builtin case split as part of ABI or raw-call work.

### C4.2: Carry forward generic builtin no-TypeError and success typing boundary
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0740 accepted the generic builtin boundary. Remaining C4 work is in type-builtins and raw-call support, not this generic builtin proof.
- Dependencies: C4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.2, E0740

#### Progress note
Preserved as completed evidence under the C4 scheduling rebase.

#### Summary
- Generic builtin no-TypeError/success typing boundary is complete.
- No executor work remains.
- This leaf stays before type-builtin work because later facts may use the same builtin typing context.

#### Statement
Already-proved generic builtin no-TypeError and success typing theorems in the reachable fresh stack.

#### Approach
No action. Treat this as stable boundary evidence for downstream evaluator/call proofs.

#### Not to try
Do not duplicate generic builtin constructor analysis inside C4.4 or C4.5.

### C4.3: Carry forward repaired type-builtin no-TypeError boundary
- Kind: `proof_group`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: C4.3.1-C4.3.3 are accepted as proved through E0745 and directly precede the remaining type-builtin success theorem.
- Dependencies: C4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3, C4.3.1, C4.3.2, C4.3.3, E0743, E0744, E0745

#### Progress note
The Extract32 repair and no-TypeError theorem remain valid and are the static interface consumed by C4.4.

#### Summary
- Carries forward the repaired `Extract32` static predicate.
- Carries forward the supported-target Extract32 no-TypeError helper.
- Carries forward the closed `well_typed_type_builtin_no_type_error` theorem.
- No executor work remains in this group.

#### Statement
Already-proved repaired `well_typed_type_builtin_no_type_error` and helper facts.

#### Approach
No action. C4.4 should use these definitions directly and should not reopen the C4.3 proof.

#### Not to try
Do not weaken the repaired `Extract32` restriction or reintroduce Bool/unsupported targets.

#### Argument
The no-TypeError theorem for type-builtins is already repaired by strengthening static admissibility for `Extract32`. This ensures the evaluator cannot choose an unsupported target type in that branch. The success-typing theorem in C4.4 should consume the same repaired static interface but need not redo its no-TypeError reasoning.

#### Definition design
The key definition interface is now `well_typed_type_builtin_args_def` plus `type_builtin_result_ok_def`. For `Extract32`, supported target bases are part of static admissibility. For ABI encode, size bounds are part of `type_builtin_result_ok_def`, not an external postulate.

#### Code structure
No edits in this carried group. New type-builtin success work should remain below the existing `Resume well_typed_type_builtin_success_type[...]` clauses in `vyperTypeBuiltinsScript.sml`.

### C4.3.1: Carry forward Extract32 static predicate repair and Bool rejection regression
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0743 proved this definition repair/regression and it remains the source-authoritative static interface.
- Dependencies: C4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3.1, E0743

#### Progress note
Carried forward under C4.3; listed explicitly so prior evidence remains visible after subtree replacement.

#### Summary
- `Extract32` static target restriction repair is complete.
- Bool/unsupported-target regression is proved.
- No remaining work.

#### Statement
Current source definitions/probes around `well_typed_type_builtin_args_def` and `extract32_result_base_ok_def` are already repaired.

#### Approach
No action.

#### Not to try
Do not alter this definition while proving ABI encode branches.

### C4.3.2: Carry forward supported Extract32 no-TypeError helper
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0744 proved the helper using the repaired static premise.
- Dependencies: C4.3.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3.2, E0744

#### Progress note
Carried forward under C4.3; no proof work remains.

#### Summary
- Supported-target Extract32 no-TypeError helper is complete.
- It is available to the finalized type-builtin no-TypeError theorem.
- No remaining work.

#### Statement
Already-proved local Extract32 no-TypeError helper in `vyperTypeBuiltinsScript.sml`.

#### Approach
No action.

#### Not to try
Do not destruct Extract32 values again in unrelated ABI branches.

### C4.3.3: Carry forward repaired `well_typed_type_builtin_no_type_error`
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: E0745 proved and built `vyperTypeBuiltinsTheory` through this theorem.
- Dependencies: C4.3.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.3.3, E0745

#### Progress note
This is the prerequisite boundary for the remaining C4.4 success typing proof.

#### Summary
- Repaired type-builtin no-TypeError theorem is complete.
- `vyperTypeBuiltinsTheory` built after this checkpoint.
- No remaining work.

#### Statement
`Theorem well_typed_type_builtin_no_type_error: ...` is already proved in current source.

#### Approach
No action. C4.4 starts after this carried theorem.

#### Not to try
Do not reopen the no-TypeError theorem while proving success typing.

### C4.4: ABI encode bound obligations (structural ancestor)
- Kind: `structural_context`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Carry-forward ancestor included only to satisfy dotted-component validation; the updated descendant C4.4.5 remains risk 2 after decomposition.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4, E0781

#### Progress note
No C4.4 sibling is replanned. This update only decomposes active child C4.4.5.

#### Summary
- Structural ancestor for ABI encode bound obligations.
- Included only so the C4.4.5 dotted subtree validates.
- No C4.4 siblings are substantively modified by this update.

#### Approach
Proceed into C4.4.5. Do not start work on C4.4 siblings from this update.

#### Not to try
Do not use this ancestor as a license to address unrelated ABI cheats or builtin cases.

#### Argument
The ABI encode bound layer proves static encoded-size estimates needed by ABI encode builtin soundness. The current update leaves the surrounding C4.4 strategy intact and repairs only the direct Vyper-to-ABI length-bound theorem by local helper decomposition.

#### Definition design
No C4.4-level definition design changes are made beyond the C4.4.5 local helper definitions.

#### Code structure
No C4.4-level file organization changes are made. All executable work remains in `semantics/prop/vyperTypeABIScript.sml`.

### C4.4.1: Carry forward already-proved typed ABI encoder wrappers
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0756 closed this component, and E0758 does not invalidate typed ABI encoder wrappers; it only shows they cannot be generalized to malformed values without extra premises.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4.1, E0756

#### Progress note
No new executor work. These wrappers remain available as auxiliary facts for genuinely ABI-typed values, but not as the core default/converted Vyper interface.

#### Summary
Already closed. Keep the typed `has_type` encoder length wrappers. They are auxiliary and must not be used to assert ABI typing of unaligned Vyper integers or defaults.

### C4.4.2: Remove the false default ABI typing attempt
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: E0757 closed this cleanup. The false `default_to_abi_has_type*` block has been removed; E0758's temporary counterexample belongs to C4.4.3 cleanup, not this component.
- Dependencies: C4.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4.2, E0757

#### Progress note
No new executor work for the old false default ABI typing cleanup.

#### Summary
Already closed. The unconditional default ABI `has_type` theorem is false and should stay deleted. Do not reintroduce byte-alignment preconditions into builtin-facing Vyper length theorems.

### C4.4.3: Add hybrid no-ABI-typing encoder length algebra
- Kind: `infrastructure_subtree`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The generic encoder algebra is now split into raw actual-length facts and static-premise corollaries. Each leaf is a standard induction over `ts`/`vs` or a wrapper around `enc_def`; no false fully no-type static-length claim remains.
- Dependencies: C4.4.2
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0758
- Invalidates prior progress/evidence: old C4.4.3 fully no-type tuple head-sum lemma, enc_tuple_head_sum_length_bound_no_type_counterexample as durable source

#### Progress note
E0758 closes the old statement as wrong and motivates this replacement. Prior failed proof work does not count toward the new lemmas except as diagnostic evidence.

#### Summary
Replace the false no-type static head-sum lemma. First remove the diagnostic counterexample theorem from source after recording it in the episode. Prove a raw tuple accumulator bound that uses actual `LENGTH (enc t v)` for static elements. Prove a monotone/static-premise corollary that may use `static_length t` only under `~is_dynamic t ==> LENGTH (enc t v) <= static_length t`. Build dynamic/fixed array wrappers with the same static premise and fixed-array length side condition.

#### Argument
The recursion of `enc_tuple` adds one head per matched `(t,v)` pair and, for dynamic elements, one tail equal to `enc t v`. Thus the unconditional invariant is exact up to list reversal/flattening and uses actual element encoding lengths. To recover ABI layout bounds, fold in a separate per-static-element side condition; this is the minimal replacement for the lost `has_type` hypothesis. Array wrappers instantiate tuple lemmas with `REPLICATE (LENGTH vs) t`; `SUM_MAP2_REPLICATE` then turns per-element bounds into `LENGTH vs * embedded`, with a final monotonic multiplication step for fixed arrays when `LENGTH vs <= n`.

#### Definition design
C4.4.3 exports local proof interfaces only; they are not public ABI typing claims. The raw lemma should be usable without any type premise and should not mention `static_length`. The static-premise corollary is the only lemma in this group whose conclusion contains `static_length` for static elements. Array wrappers must expose assumptions in the shape downstream Vyper proofs can supply: `!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound`, `~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t`, embedded-size inequality, and for fixed arrays `LENGTH vs <= n`.

#### Code structure
Place these lemmas in `vyperTypeABIScript.sml` where the old C4.4.3 lemmas were, before Vyper dynamic/static bridge lemmas. Use `contractABITheory.enc_def`, `LENGTH_FLAT`, `REV_REVERSE_LEM`, `MAP_REVERSE`, `SUM_REVERSE`, `SUM_APPEND`, and `LENGTH_enc_number`; do not unfold `contractABITheory.has_type_def` in this component.

### C4.4.3.0: Remove the diagnostic false no-type counterexample theorem
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The EVAL counterexample is valid evidence but should not remain in the final proof script as a durable local theorem once the PLAN is repaired.
- Carries progress/evidence from: E0758

#### Progress note
The counterexample remains documented in E0758 and this PLAN. Source should instead contain the repaired lemmas.

#### Summary
Delete `enc_tuple_head_sum_length_bound_no_type_counterexample` from `semantics/prop/vyperTypeABIScript.sml`. Verify that the build still reaches the known `vyper_to_abi_enc_length_bound` probe or the next new C4.4.3 lemma. Do not delete any proved dynamic/static/embedded bridge lemmas.

#### Approach
This is a mechanical edit. Remove only the local counterexample theorem block added for E0758. The expected build state after deletion is unchanged except that this theorem name no longer exists.

#### Not to try
Do not keep the counterexample as a permanent regression theorem in the source; the final task is a clean soundness stack, not a catalog of abandoned lemma shapes.

### C4.4.3.1: Prove raw tuple accumulator bound with actual element encoding lengths
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: This follows directly by induction on `ts` with a case split on `vs`, mirroring the existing typed `enc_tuple_acc_length_bound` but replacing the static branch contribution by `LENGTH (enc t v)`.
- Dependencies: C4.4.3.0

#### Summary
Prove the unconditional tuple-accumulator length lemma. It must not assume `has_types` or any ABI validity. Static and dynamic elements are both bounded by their actual encoded lengths; dynamic elements additionally contribute the 32-byte offset head.

#### Statement
Theorem enc_tuple_acc_length_bound_actual[local]:
  !ts vs hl tl hds tls.
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else LENGTH (enc t v)) ts vs)

#### Approach
Induct on `ts` and case split on `vs`. The mismatched-list base cases use the final `enc_tuple` catch-all and `FLAT/REV` length rewrites. In the matched cons case unfold one step of `enc_tuple`; for dynamic elements use `LENGTH_enc_number = 32` for the offset head and put `enc t v` into tails, while for static elements put `enc t v` into heads and no tail.

#### Not to try
Do not try to prove a no-premise bound with `static_length t` in the static branch; E0758 shows it is false for `Tuple []` paired with `NumV 0`. Do not import `has_type` here; this lemma is intentionally raw encoder algebra.

### C4.4.3.2: Prove static-premise tuple head-sum corollary
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: A simple list induction over `ts`/`vs` or a MAP2/SUM monotonic helper converts the raw actual-length sum into the old static-head shape under an explicit static-element length premise.
- Dependencies: C4.4.3.1

#### Summary
Recover the old useful tuple bound, but only with the missing static-element premise. This is the boundary lemma downstream Vyper conversions should use when they can prove each static converted/default element encodes within its static ABI size.

#### Statement
Theorem enc_tuple_acc_length_bound_static_premise[local]:
  !ts vs hl tl hds tls.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)

Theorem enc_tuple_length_bound_static_premise[local]:
  !ts vs.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    LENGTH (enc (Tuple ts) (ListV vs)) <=
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)

#### Approach
First prove a small SUM/MAP2 monotonic fact by induction on `ts` and case split on `vs`, or prove the corollary directly with the raw accumulator lemma plus that induction. For the tuple wrapper, unfold `enc_def` once and instantiate the accumulator with `head_lengths ts 0`, `0`, `[]`, `[]`. Keep the premise over `ZIP (ts,vs)` so cons-step membership facts simplify naturally.

#### Not to try
Do not encode the premise as an ABI `has_types ts vs` assumption; that reintroduces the unaligned-integer problem. Avoid manual large theorem instantiations in consumers; this lemma's conclusion should match the tuple wrapper use site directly.

### C4.4.3.3: Prove replicated MAP2 embedded-size bound under static premise
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: This is a small variant of the existing `SUM_MAP2_REPLICATE_enc_bound`, with an extra static-element premise used only when `is_dynamic t` is false.
- Dependencies: C4.4.3.2

#### Summary
Adapt the replicated element-sum bound so it can consume the static-premise tuple corollary. Dynamic elements use the per-element `elem_bound`; static elements use the explicit `LENGTH (enc t v) <= static_length t` premise and the embedded-size inequality.

#### Statement
Theorem SUM_MAP2_REPLICATE_enc_bound_static_premise[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
              (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded

#### Approach
Induct on `vs`. In the step case, specialize the IH to the tail and use the MEM premise for `h`. Split on `is_dynamic t`; dynamic uses `elem_bound`, static uses the static premise and the embedded inequality.

#### Not to try
Do not try to reuse the old no-premise replicated bound if it assumes static elements already have `static_length`; the premise is the whole repair.

### C4.4.3.4: Prove dynamic and fixed array no-ABI-typing wrappers with static premises
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 40
- Work units: 3
- Rationale: These wrappers are straightforward instantiations of the static-premise tuple lemma on `REPLICATE (LENGTH vs) t`, plus the replicated SUM bound. Fixed arrays need an explicit `LENGTH vs <= n` side condition because the encoder uses the actual value-list length.
- Dependencies: C4.4.3.3
- Checkpoint: yes
- Invalidates prior progress/evidence: old enc_dyn_array_same_length_bound/enc_fixed_array_same_length_bound as core no-type wrappers if they require ABI has_type

#### Summary
Provide the array interfaces needed by Vyper same/sparse conversions. Dynamic arrays add a 32-byte length prefix and then tuple-encode actual elements. Fixed arrays tuple-encode actual elements and are bounded by `n * embedded` when `LENGTH vs <= n`. No ABI `has_type` premise is used.

#### Statement
Theorem enc_dyn_array_same_length_bound_static_premise[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc (Array NONE t) (ListV vs)) <= 32 + LENGTH vs * embedded

Theorem enc_fixed_array_same_length_bound_static_premise[local]:
  !n t vs elem_bound embedded.
    (LENGTH vs <= n /\
     (!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc (Array (SOME n) t) (ListV vs)) <= n * embedded

#### Approach
Unfold `enc_def` once for each array. Instantiate `enc_tuple_acc_length_bound_static_premise` or the tuple wrapper on `REPLICATE (LENGTH vs) t` and `vs`; the ZIP/MEM static premise reduces to the supplied `MEM v vs` premise. Apply the replicated SUM bound, then arithmetic; for fixed arrays use multiplication monotonicity from `LENGTH vs <= n`.

#### Not to try
Do not depend on `contractABI.has_type_def` to get fixed-array length equality. In this repaired interface the converter/sparse proof supplies `LENGTH vs <= n` (usually equality) explicitly.

### C4.4.4: Default ABI encode-length bridge (structural ancestor)
- Kind: `structural_context`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Carry-forward parent for the edited C4.4.4.3 subtree; the replacement relies on already-proved C4.4.4.2 tuple helpers.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C4.4.4, C4.4.4.2.1, C4.4.4.2.2, C4.4.4.2.3, C4.4.4.2.4

#### Progress note
Structural parent only. C4.4.4.2 tuple boundary progress carries forward and is consumed by the new C4.4.4.3 leaves.

#### Summary
Structural parent for default ABI bridge work. C4.4.4.2 tuple LIST_REL/SUM/static helpers are assumed closed and carried forward. This update replaces only the brittle C4.4.4.3 proof plan.

#### Argument
Default ABI length bounds are assembled in layers: element bounds, tuple LIST_REL boundaries, evaluator recursion over type/type-list evaluation, then packaging corollaries. This scoped update affects the evaluator-recursion layer only and intentionally consumes, rather than reopens, the tuple boundary layer.

#### Definition design
Use `default_to_abi_elem_bound_rel` as the interface between element evaluation and tuple consumers. The failure sign is any downstream proof needing to unfold `enc_tuple` where a LIST_REL boundary lemma should apply.

#### Code structure
Keep all helper lemmas local in `semantics/prop/vyperTypeABIScript.sml`. Insert new C4.4.4.3 helper immediately after `default_to_abi_tuple_bound_from_LIST_REL`; leave later downstream theorem blocks untouched.

### C4.4.4.1: Audit and preserve existing Vyper dynamic/static and array-default length bridges
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is a mechanical source audit: the relevant helper lemmas are already present in the current file, and the executor only needs to ensure they remain available before replacing the failed theorem body.
- Progress transition: `refinement`
- Carries progress/evidence from: source lines around vyperTypeABIScript.sml:430-545, E0770 source audit

#### Progress note
E0770 read evidence confirms the fixed-array default helper is present and the stale monolithic theorem starts immediately after it.

#### Summary
Confirm that the existing local helpers for Vyper ABI dynamic/static length and fixed-array defaults are present and usable. Do not edit their statements unless build errors force trivial name/import fixes. This leaf prepares the file for the C4.4.4.2-.4 replacement.

#### Approach
Check `vyper_to_abi_type_dynamic`, `vyper_to_abi_static_length_bound`, `vyper_to_abi_embedded_head_bound`, `enc_fixed_array_replicate_tuple_bound_static_premise`, and `default_fixed_array_replicate_tuple_bound_from_elem`. If all are present, record progress and proceed; no holbuild is required unless the file has been changed.

#### Not to try
Do not try to resume or repair the old `default_to_abi_enc_length_bound_eval` here. This component is only an audit/carry-forward boundary.

### C4.4.4.2: Prove tuple default-encoding bounds from per-element default bounds
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The planned proof remains a standard LIST_REL/list-sum bound after naming the element predicate; the current issue is that its children were queued but not made to block downstream leaves.
- Dependencies: C4.4.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Carries forward the decomposition guidance; only dependency metadata is repaired.

#### Summary
Prove the exact local theorem `default_to_abi_tuple_bound_from_LIST_REL` after C4.4.4.1. Execute children C4.4.4.2.1-.4 in dependency order. This subtree must close before C4.4.4.3, C4.4.4.4, and C4.4.5 are attempted.

#### Description
Replace the current partial/brittle proof block with the local helper family already described: element predicate, head embedded-size bound, static ZIP premise helper, SUM_MAP2 bound helper, and final tuple bound. Run `holbuild build vyperTypeABITheory` after C4.4.4.2.4 closes.

#### Statement
Culminates in the existing local theorem `default_to_abi_tuple_bound_from_LIST_REL` in `semantics/prop/vyperTypeABIScript.sml`; keep its statement unchanged.

#### Approach
Follow the child components in order. Do not start downstream ABI leaves while this source block is partial or while `vyperTypeABITheory` fails here.

#### Not to try
Do not bypass this failed source state by beginning C4.4.5; C4.4.5 assumes the default bridge checkpoint is available.

#### Argument
The LIST_REL premise supplies per-element default encoding and static-length facts. C4.4.4.2.1 turns those into a pointwise embedded-size head bound; C4.4.4.2.2 supplies the static premise for tuple layout; C4.4.4.2.3 bounds the MAP2/SUM by list induction; C4.4.4.2.4 composes those two bounds.

#### Definition design
The local element relation is only a proof-interface device to stabilize LIST_REL consumers. Downstream children should use the relation/head-bound lemma rather than manually manipulating the anonymous lambda.

#### Code structure
Place the helper definition and local theorems immediately before the existing `default_to_abi_tuple_*` block in `semantics/prop/vyperTypeABIScript.sml`.

### C4.4.4.2.1: Name the per-element default ABI bound relation and prove the head embedded-size bound
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Direct use of the existing `vyper_to_abi_embedded_head_bound`; low risk once scheduled before its consumers.
- Dependencies: C4.4.4.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Same leaf obligation as the decomposition; now explicitly first after the C4.4.4.1 audit.

#### Summary
Add the local element relation and prove the one-element embedded-size head bound. This is the first executable repair leaf for the currently failing tuple-bound block.

#### Statement
Use the previously specified `default_to_abi_elem_bound_rel_def[local]` and `default_to_abi_elem_embedded_size_bound[local]` interfaces.

#### Approach
Unfold the relation, apply `vyper_to_abi_embedded_head_bound`, split on `is_dynamic (vyper_to_abi_type tenv typ)`, and finish arithmetically.

#### Not to try
Do not prove downstream ZIP or SUM facts before this lemma exists; they should consume this pointwise interface.

### C4.4.4.2.2: Prove the static ZIP premise helper from LIST_REL
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: Routine list induction/MEM_ZIP proof once C4.4.4.2.1 is present.
- Dependencies: C4.4.4.2.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001, E0772

#### Progress note
Same helper; dependency on the named element relation is made explicit.

#### Summary
Re-establish `default_to_abi_tuple_static_premise_from_LIST_REL`. It supplies the static premise for `enc_tuple_length_bound_static_premise` and must precede the final tuple-bound theorem.

#### Statement
Keep the existing local theorem statement `default_to_abi_tuple_static_premise_from_LIST_REL[local]` unchanged.

#### Approach
Induct on `ts` with `tvs` generalized, case split `tvs`, simplify `vyper_to_abi_type_def` and `MEM_ZIP`, use `vyper_to_abi_type_dynamic` in the head static case, and apply the IH in the tail case.

#### Not to try
Do not combine this with the SUM_MAP2 proof or unfold tuple encoding.

### C4.4.4.2.3: Prove the tuple SUM_MAP2 bound from LIST_REL
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Standard head-plus-tail list induction after the pointwise lemma; no unprovability evidence.
- Dependencies: C4.4.4.2.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Same helper; dependency on the pointwise embedded-size lemma is made explicit.

#### Summary
Prove the exact `SUM (MAP2 ...) <= vyper_abi_size_bound_list` helper. This is independent of the static ZIP helper but depends on the pointwise embedded-size bound.

#### Statement
Keep the existing local theorem statement `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL[local]` unchanged.

#### Approach
Induct on `ts` with `tvs` generalized. In the cons case, split the LIST_REL premise into head and tail facts, use `default_to_abi_elem_embedded_size_bound` on the head, the IH on the tail, and finish with `vyper_abi_size_bound_def` and arithmetic.

#### Not to try
Do not manually fight anonymous-lambda IH matching; rewrite/use the named element relation from C4.4.4.2.1.

### C4.4.4.2.4: Prove the final tuple default-encoding length bound from LIST_REL
- Kind: `target_theorem`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: Direct transitivity once the static ZIP and SUM_MAP2 helpers are proved.
- Dependencies: C4.4.4.2.2, C4.4.4.2.3
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m41942_t001

#### Progress note
Same final leaf, now explicitly waits for both boundary helpers. Checkpoint is retained because successful build through this block unblocks downstream default ABI work.

#### Summary
Prove `default_to_abi_tuple_bound_from_LIST_REL`. After closing this leaf, run `holbuild build vyperTypeABITheory` to verify the partial source block is repaired before proceeding.

#### Statement
Keep the existing local theorem statement `default_to_abi_tuple_bound_from_LIST_REL[local]` unchanged.

#### Approach
Use `enc_tuple_length_bound_static_premise` plus C4.4.4.2.2 to bound tuple encoding by the MAP2/SUM expression, then C4.4.4.2.3 to bound the SUM by `vyper_abi_size_bound_list`; finish by transitivity/arithmetic.

#### Not to try
Do not unfold `enc` or tuple layout; the proof should be a boundary-lemma composition.

### C4.4.4.3: Default ABI bounds via evaluator LIST_REL invariant
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The unproven arithmetic/tuple accumulator branch is eliminated. Remaining work is a standard recursion-matching induction plus a packaging corollary using already-proved local tuple boundary lemmas.
- Dependencies: C4.4.4.2
- Progress transition: `refinement`
- Carries progress/evidence from: C4.4.4.3, E0777, C4.4.4.2.1, C4.4.4.2.2, C4.4.4.2.3, C4.4.4.2.4
- Invalidates prior progress/evidence: C4.4.4.3 monolithic accumulator proof attempt in E0777

#### Progress note
Prior progress established that the theorem statement needed a SUM_MAP2 conjunct and that tuple LIST_REL helpers are closed. The failed accumulator proof does not carry forward tactically; the strengthened helper shape below replaces it while preserving the same task obligation.

#### Summary
Replace the brittle direct proof of `default_to_abi_enc_length_bound_eval` with a stronger local helper that follows `evaluate_type_ind`. The helper returns `default_to_abi_elem_bound_rel` for a single evaluated type and a `LIST_REL default_to_abi_elem_bound_rel` for the fresh suffix produced by `evaluate_types`. The exact theorem then follows by applying `default_to_abi_tuple_bound_from_LIST_REL`, `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL`, and `default_to_abi_tuple_static_premise_from_LIST_REL`. Do not reason about `enc_tuple` accumulators in the `evaluate_types` cons case.

#### Description
This component owns only the local mutual default-ABI bound theorem around lines 651-759 of `semantics/prop/vyperTypeABIScript.sml`. The previous direct proof exposed goals about `enc_tuple (head_lengths (head::tail) 0) ...` with accumulated head/tail byte lists; that is the wrong interface for evaluator recursion. The recursion naturally constructs the semantic type-value list suffix, not an ABI tuple encoding accumulator. Prove that suffix as a `LIST_REL` of element bounds, then consume the tuple boundary lemmas already proved in C4.4.4.2.

#### Approach
First prove the stronger helper by `ho_match_mp_tac evaluate_type_ind`. The only list-accumulator work should be choosing `dtvs = []` in the nil case and `dtvs = tv::tail_dtvs` in the cons case; all ABI tuple encoding bounds belong in the single-type tuple constructor case or the final packaging theorem. Reuse the existing successful per-type case proof fragments for base, bytes, arrays, and fixed arrays, but route tuple cases through the LIST_REL tuple helper rather than through `enc_tuple_acc_length_bound_static_premise`.

#### Not to try
Do not keep patching the old monolithic `TRY` chain by adding more `qmatch_goalsub_abbrev_tac` or `FIRST_ASSUM` steps around `head_lengths`; E0777 showed this is a proof-interface problem, not a missing arithmetic rewrite. Do not unfold tuple encoding in the `evaluate_types` cons branch. Do not edit `vyper_to_abi_enc_length_bound` or downstream builtin/call files while this local theorem is unresolved.

#### Argument
For `evaluate_types tenv ts acc = SOME tvs`, the evaluator uses `acc` only as a reverse prefix of already-evaluated type values. The semantic invariant is therefore: there exists a fresh suffix `dtvs` such that `tvs = REVERSE acc ++ dtvs` and each source type in `ts` is related to its corresponding fresh type value by `default_to_abi_elem_bound_rel`. In the cons case, the recursive call on the tail with accumulator `tv::acc` yields `tvs = REVERSE (tv::acc) ++ tail_dtvs`; choose the caller's suffix as `tv::tail_dtvs`, and the equality reduces to `REVERSE acc ++ [tv] ++ tail_dtvs = REVERSE acc ++ (tv::tail_dtvs)`. For a tuple type in the single-type conjunct, the list IH gives exactly this `LIST_REL` for the elements, and `default_to_abi_tuple_bound_from_LIST_REL` supplies the tuple encoding bound. Once this stronger relation is proved, the public exact theorem is a corollary: unwrap the relation for the first conjunct, and for the list conjunct apply the tuple length, SUM_MAP2, and static ZIP boundary lemmas to the fresh suffix.

#### Definition design
Do not add a new datatype or executable definition. Reuse the existing local relation `default_to_abi_elem_bound_rel_def` as the proof interface: it packages `(evaluate_type tenv typ = SOME tv)`, the default ABI encoded-length bound, and the static bound needed by tuple encoders. Add one local theorem, before `default_to_abi_enc_length_bound_eval`, with a mutual statement over `evaluate_type`/`evaluate_types` that returns this relation and a `LIST_REL` of this relation. The failure sign for this design is any remaining need in the `evaluate_types` cons branch to unfold `contractABITheory.enc_def` or to instantiate `enc_tuple_acc_length_bound_static_premise`; if that happens, the proof has drifted back to the old bad interface.

#### Code structure
All edits are local to `semantics/prop/vyperTypeABIScript.sml` near the existing default ABI helper block. Insert the new local theorem immediately after `default_to_abi_tuple_bound_from_LIST_REL` and before `default_to_abi_enc_length_bound_eval`. Then replace the body of `default_to_abi_enc_length_bound_eval` with a short corollary proof from the new helper and the three C4.4.4.2 tuple boundary lemmas. Leave `vyper_to_abi_enc_length_bound` and builtin consumers untouched in this component.

### C4.4.4.3.1: Prove LIST_REL helper for evaluated default ABI elements
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: This is the natural induction invariant for `evaluate_type_ind`; the hard accumulator tuple goal disappears, and the remaining type cases can reuse existing local bound helpers.
- Dependencies: C4.4.4.2
- Checkpoint: yes
- Carries progress/evidence from: E0777, C4.4.4.2.1, C4.4.4.2.2, C4.4.4.2.3, C4.4.4.2.4

#### Progress note
E0777 contributes the diagnosis and confirms the strengthened list theorem needs a SUM bound later; C4.4.4.2 contributes the tuple boundary lemmas used in tuple type cases.

#### Summary
Add and prove a local mutual helper, tentatively named `default_to_abi_elem_bound_rel_eval`. The first conjunct proves `default_to_abi_elem_bound_rel tenv typ tv` from `evaluate_type tenv typ = SOME tv`. The second conjunct proves that `evaluate_types` returns `REVERSE acc` plus a fresh suffix related to the source types by `LIST_REL default_to_abi_elem_bound_rel`. This helper is the durable replacement for the brittle accumulator-level proof branch.

#### Statement
Theorem default_to_abi_elem_bound_rel_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     default_to_abi_elem_bound_rel tenv typ tv) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     ?dtvs.
       tvs = REVERSE acc ++ dtvs /\
       LIST_REL (default_to_abi_elem_bound_rel tenv) ts dtvs)

#### Approach
Use `ho_match_mp_tac evaluate_type_ind`, then simplify with `evaluate_type_def`, `default_to_abi_elem_bound_rel_def`, `default_to_abi_def`, `default_to_abi_list_MAP`, `default_to_abi_fields_MAP`, `vyper_to_abi_type_def`, `vyper_abi_size_bound_def`, `AllCaseEqs()`, `LET_THM`, and the byte length facts already used by the old proof. In the tuple type case, destruct the list IH for `evaluate_types ... []`, rewrite the suffix equality to obtain the actual element list, and apply `default_to_abi_tuple_bound_from_LIST_REL`; for the static conjunct use the proved length bound plus `vyper_to_abi_static_length_bound` after `vyper_to_abi_type_dynamic` relates source and ABI dynamicness. In the `evaluate_types` cons case, use the head type IH for `default_to_abi_elem_bound_rel tenv typ tv`, use the tail list IH, choose `tv::dtvs`, and solve with `LIST_REL` simplification and `REVERSE_DEF`/append simplification; there should be no ABI encoding subgoal in this branch.

#### Not to try
Do not include the exact theorem's tuple `LENGTH`, `SUM MAP2`, or static ZIP conclusions in this helper's `evaluate_types` conjunct. Those are consumer facts derivable from `LIST_REL`; putting them in the recursive invariant recreates the head-plus-tail accumulator problem. Do not instantiate `enc_tuple_acc_length_bound_static_premise` in this helper's list cons branch.

### C4.4.4.3.2: Derive exact default_to_abi_enc_length_bound_eval from LIST_REL helper
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 10
- Work units: 3
- Rationale: Once the LIST_REL helper is proved, the exact theorem is only projection and application of already-closed tuple boundary lemmas.
- Dependencies: C4.4.4.3.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C4.4.4.3, E0777
- Invalidates prior progress/evidence: old direct proof body of default_to_abi_enc_length_bound_eval

#### Progress note
This leaf completes the original theorem obligation using the repaired interface; previous direct proof progress is intentionally replaced by a short corollary proof.

#### Summary
Replace the body of `default_to_abi_enc_length_bound_eval` with a short proof from `default_to_abi_elem_bound_rel_eval`. The single-type conjunct unfolds the relation and projects the encoded-length bound. The list conjunct obtains `dtvs` and `LIST_REL`, then calls the tuple length, SUM_MAP2, and static ZIP boundary lemmas. This is the theorem named in the task and is a checkpoint because it unblocks the downstream default ABI packaging corollaries.

#### Statement
Theorem default_to_abi_enc_length_bound_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
     vyper_abi_size_bound tenv typ) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     ?dtvs.
       tvs = REVERSE acc ++ dtvs /\
       LENGTH (enc (Tuple (vyper_to_abi_types tenv ts))
                   (ListV (MAP default_to_abi dtvs))) <=
       vyper_abi_size_bound_list tenv ts /\
       SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                            else static_length t)
                 (vyper_to_abi_types tenv ts) (MAP default_to_abi dtvs)) <=
       vyper_abi_size_bound_list tenv ts /\
       (!t v. MEM (t,v) (ZIP (vyper_to_abi_types tenv ts,
                               MAP default_to_abi dtvs)) /\
              ~is_dynamic t ==>
              LENGTH (enc t v) <= static_length t))

#### Approach
For conjunct 1, `drule (cj 1 default_to_abi_elem_bound_rel_eval)` and simplify with `default_to_abi_elem_bound_rel_def`. For conjunct 2, `drule (cj 2 default_to_abi_elem_bound_rel_eval)`, choose the returned `dtvs`, and keep the `LIST_REL` fact. Each of the three remaining conjuncts should be solved by applying respectively `default_to_abi_tuple_bound_from_LIST_REL`, `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL`, and `default_to_abi_tuple_static_premise_from_LIST_REL`, with `default_to_abi_elem_bound_rel_def` unfolded only enough to match their expected lambda relation.

#### Not to try
Do not copy the old proof's large `TRY` blocks into this theorem. Do not prove tuple length or SUM facts by unfolding `contractABITheory.enc_def`; the whole point of C4.4.4.2 was to provide these boundary lemmas. If matching a tuple helper requires manual theorem plumbing, add a tiny local assertion converting `LIST_REL (default_to_abi_elem_bound_rel tenv) ts dtvs` to the helper's lambda relation by `fs[default_to_abi_elem_bound_rel_def]`, rather than instantiating every argument manually.

### C4.4.4.4: Derive compatibility default ABI length theorem and static corollary
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: Wrapper/corollary work is mechanical once both default ABI bridge inputs are available.
- Dependencies: C4.4.4.2.4, C4.4.4.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: prior C4.4.4.4 plan

#### Progress note
Adds explicit dependencies on the tuple-bound theorem and mutual invariant before the compatibility checkpoint.

#### Summary
Package the compatibility default ABI length theorem and static corollary only after C4.4.4.2.4 and C4.4.4.3. Closing this checkpoint authorizes direct ABI theorem work in C4.4.5.

#### Approach
Derive by projections/composition from the mutual invariant and tuple-bound bridge; build `vyperTypeABITheory` at the end.

#### Not to try
Do not start C4.4.5 before this checkpoint closes.

### C4.4.5: Prove direct mutual Vyper-to-ABI encoded-length theorem via local ABI-bound relations
- Kind: `boundary_lemma_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The remaining proof is standard once conversion success is factored into element/list/same/sparse ABI-value bound relations. Existing tuple/array static-premise lemmas and default_to_abi bounds cover the hard size arithmetic; the main new design point is the sparse IH predicate independent of the array length.
- Progress transition: `refinement`
- Carries progress/evidence from: E0781, C4.4.5

#### Progress note
E0781 validated that the old direct induction reaches only local ABI length-bound obligations and identified the brittle monolithic proof suffix. Prior progress on existing helpers in `vyperTypeABIScript.sml` is carried forward, but the proof strategy for the main theorem is refined into explicit local relation/boundary components.

#### Summary
- Replace the broad `TRY`/case-analysis suffix in `vyper_to_abi_enc_length_bound` with local relation infrastructure.
- Package encoded ABI values by their static Vyper type and runtime type, independent of their source Vyper value where possible.
- Prove tuple/dynamic-array/fixed-array consumers from these relations using existing `enc_*_static_premise` lemmas.
- Strengthen the mutual conversion theorem so list/same/sparse branches return reusable bound relations, then derive the exported theorem as a corollary.
- For sparse arrays, use a value-typed predicate independent of the current recursion length; do not require `sparse_has_type tv n sparse` in the recursive IH.

#### Description
This component owns only `semantics/prop/vyperTypeABIScript.sml` local helpers immediately preceding `vyper_to_abi_enc_length_bound` and the proof of that theorem. The theorem statement should remain the current source statement. Internal helper statements may be added locally. The final public theorem should expose exactly the four-conjunct length-bound theorem currently named `vyper_to_abi_enc_length_bound`, because downstream ABI encode builtin cases wait on it.

#### Approach
Proceed by adding the relation definitions, proving consumer boundary lemmas, proving the strengthened mutual theorem, then deriving the existing theorem. The induction variable for the strengthened theorem is exactly `vyper_to_abi_ind`; the strengthened sparse conjunct is what makes the induction align with the recursive call on `n`.

#### Not to try
Do not continue extending the current broad `TRY (Cases_on v >> gvs[...] >> ...)` suffix; E0781 shows it leaves heterogeneous goals and obscures the needed invariants. Do not formulate the sparse strengthened IH with `sparse_has_type tv n sparse`: in the `SUC n` case, the sparse map may contain key `n`, so `sparse_has_type tv (SUC n) sparse` does not imply `sparse_has_type tv n sparse`. Do not duplicate tuple/array encoding arithmetic in the main mutual proof; use the existing `enc_tuple_length_bound_static_premise`, `enc_dyn_array_same_length_bound_static_premise`, and `enc_fixed_array_same_length_bound_static_premise` through boundary lemmas.

#### Argument
The conversion functions recursively produce ABI values whose encoded length is bounded by the static ABI size computed from the Vyper type. Instead of re-proving tuple/array arithmetic in every evaluator branch, define an element relation `abi_av_bound_rel tenv typ tv av` that records `evaluate_type tenv typ = SOME tv` and the direct encoded length bound for the converted ABI value `av`. Define a heterogeneous list relation `abi_av_list_bound_rel tenv ts avs tvs` as the pointwise version of this element relation.

From the heterogeneous relation, tuple encoding is bounded by `vyper_abi_size_bound_list`: first derive the static-element premise required by `enc_tuple_length_bound_static_premise` using `vyper_to_abi_type_dynamic` and `vyper_to_abi_static_length_bound`, then prove the `SUM MAP2` bound by induction over the relation, mirroring the existing `default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL`. From an `EVERY (abi_av_bound_rel tenv typ tv) avs`, dynamic and fixed same-type arrays are bounded by the existing `enc_dyn_array_same_length_bound_static_premise` and `enc_fixed_array_same_length_bound_static_premise` plus `vyper_to_abi_embedded_head_bound`.

The strengthened mutual theorem follows `vyper_to_abi_ind`. Its first conjunct proves `abi_av_bound_rel` for each successful `vyper_to_abi`; its second proves `abi_av_list_bound_rel` for `vyper_to_abi_list`; its third proves `EVERY abi_av_bound_rel` and length preservation for `vyper_to_abi_same`; its fourth proves `EVERY abi_av_bound_rel` and `LENGTH avs = n` for `vyper_to_abi_sparse`. The sparse conjunct must assume only that every value occurring in `sparse` has type `tv`, not `sparse_has_type tv n sparse`, because the recursive call decrements `n` while the sparse map may still contain key `n`. The exported theorem is then a direct corollary: apply the relevant strengthened conjunct and the tuple/array boundary lemmas; convert `sparse_has_type` to the length-independent sparse value predicate for the public sparse conjunct.

#### Definition design
Add only local definitions in `vyperTypeABIScript.sml`:

1. `abi_av_bound_rel tenv typ tv av` packages `evaluate_type tenv typ = SOME tv` and `LENGTH (enc (vyper_to_abi_type tenv typ) av) <= vyper_abi_size_bound tenv typ`. Do not include source value/conversion success in this relation; the relation should also cover default ABI values used by sparse arrays.
2. `abi_av_list_bound_rel tenv ts avs tvs` is a recursive four-list relation matching `ts`, converted ABI values `avs`, and runtime type values `tvs` pointwise with `abi_av_bound_rel`.
3. `sparse_values_have_type tv sparse` is the length-independent predicate `!k v. MEM (k,v) sparse ==> value_has_type tv v`.

Boundary behavior expected from these definitions:
- `abi_av_bound_rel` plus non-dynamic ABI type should imply the static-length premise by `vyper_to_abi_type_dynamic` and `vyper_to_abi_static_length_bound`.
- `abi_av_list_bound_rel` should imply the tuple `SUM MAP2` bound, the static-element premise, and finally the tuple `enc` length bound.
- `EVERY (abi_av_bound_rel tenv typ tv) avs` should feed the existing same-type array static-premise lemmas.
- `sparse_values_have_type` should be stable across recursive calls of `vyper_to_abi_sparse`; this is the empirical failure sign to avoid if a proof tries to use `sparse_has_type tv n sparse` as the sparse IH premise.

#### Code structure
All edits for this subtree belong in `semantics/prop/vyperTypeABIScript.sml`, after the existing default ABI bound helpers (`default_to_abi_enc_length_bound`, `default_to_abi_static_enc_length_bound`) and before `vyper_to_abi_enc_length_bound`. Keep new definitions and helper theorems `[local]` unless a downstream file later explicitly needs them; the only exported output from this component should remain `vyper_to_abi_enc_length_bound`. Replace the current proof body of `vyper_to_abi_enc_length_bound` with a short compatibility proof from the strengthened local theorem. Do not move ABI arithmetic helpers to another theory or introduce dependencies outside the fresh stack.

### C4.4.5.1: Add local ABI-value bound and sparse-value predicates
- Kind: `definition_infrastructure`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: These are simple local recursive/predicate definitions with no hard proof content. They only package facts already present in existing goals and avoid source-value dependence for default sparse elements.

#### Progress note
New local infrastructure introduced to decompose the E0781 failing theorem.

#### Summary
- Define `abi_av_bound_rel` for a single ABI value produced for a Vyper type.
- Define `abi_av_list_bound_rel` for heterogeneous tuples/lists of ABI values.
- Define `sparse_values_have_type` as a length-independent sparse value typing predicate.
- Place definitions locally before `vyper_to_abi_enc_length_bound`.

#### Statement
```sml
Definition abi_av_bound_rel_def[local]:
  abi_av_bound_rel tenv typ tv av <=>
    evaluate_type tenv typ = SOME tv /\
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
      vyper_abi_size_bound tenv typ
End

Definition abi_av_list_bound_rel_def[local]:
  abi_av_list_bound_rel tenv [] [] [] = T /\
  abi_av_list_bound_rel tenv (typ::ts) (av::avs) (tv::tvs) =
    (abi_av_bound_rel tenv typ tv av /\
     abi_av_list_bound_rel tenv ts avs tvs) /\
  abi_av_list_bound_rel tenv _ _ _ = F
End

Definition sparse_values_have_type_def[local]:
  sparse_values_have_type tv sparse <=>
    !k v. MEM (k,v) sparse ==> value_has_type tv v
End
```

#### Approach
Add these definitions as local infrastructure. Keep `abi_av_bound_rel` deliberately minimal: static-length consequences should be derived by boundary lemmas, not stored in the definition. The list relation should recurse on all three lists so that `simp[abi_av_list_bound_rel_def]` gives length alignment by cases.

#### Not to try
Do not include `vyper_to_abi ... = SOME av` or `value_has_type tv v` in `abi_av_bound_rel`; sparse default entries have no source conversion premise but still need the same encoded-bound interface. Do not define sparse typing in terms of `n`, because the sparse conversion recursion decreases `n` while reusing the same sparse map.

### C4.4.5.2: Prove ABI-bound relation consumer lemmas for tuples and same-type arrays
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The proofs are standard inductions/reuses of existing static-premise encoding lemmas. The helper conclusions match the use sites in the strengthened mutual theorem and final compatibility corollary.
- Dependencies: C4.4.5.1

#### Progress note
New helper layer replacing monolithic arithmetic in the failed proof.

#### Summary
- Derive static-element premises from `abi_av_bound_rel` using dynamic/static type facts.
- Derive a `SUM MAP2` tuple bound from `abi_av_list_bound_rel`.
- Derive tuple `enc` length bound from the relation.
- Derive dynamic and fixed same-type array bounds from `EVERY abi_av_bound_rel`.

#### Statement
```sml
Theorem abi_av_bound_rel_static_premise[local]:
  !tenv typ tv av.
    abi_av_bound_rel tenv typ tv av /\
    ~is_dynamic (vyper_to_abi_type tenv typ) ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    static_length (vyper_to_abi_type tenv typ)

Theorem abi_av_list_static_premise[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    !t av.
      MEM (t,av) (ZIP (vyper_to_abi_types tenv ts, avs)) /\ ~is_dynamic t ==>
      LENGTH (enc t av) <= static_length t

Theorem abi_av_list_SUM_MAP2_bound[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    SUM (MAP2 (\t av. if is_dynamic t then 32 + LENGTH (enc t av)
                          else static_length t)
              (vyper_to_abi_types tenv ts) avs) <=
    vyper_abi_size_bound_list tenv ts

Theorem abi_av_list_tuple_bound[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound_list tenv ts

Theorem abi_avs_dyn_array_bound[local]:
  !tenv typ tv avs.
    evaluate_type tenv typ = SOME tv /\
    EVERY (abi_av_bound_rel tenv typ tv) avs ==>
    LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    32 + LENGTH avs * vyper_abi_embedded_size tenv typ

Theorem abi_avs_fixed_array_bound[local]:
  !tenv typ tv n avs.
    evaluate_type tenv typ = SOME tv /\
    EVERY (abi_av_bound_rel tenv typ tv) avs /\
    LENGTH avs <= n ==>
    LENGTH (enc (Array (SOME n) (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    n * vyper_abi_embedded_size tenv typ
```

#### Approach
For `abi_av_bound_rel_static_premise`, unfold the relation, use `vyper_to_abi_type_dynamic` to convert the `is_dynamic` assumption to `~vyper_is_dynamic`, then use `vyper_to_abi_static_length_bound`. Prove the list static and SUM lemmas by induction on `ts` with cases on `avs` and `tvs`, simplifying `abi_av_list_bound_rel_def`, `vyper_to_abi_type_def`, and `vyper_abi_size_bound_def`. The tuple and array bounds should be short wrappers around existing `enc_*_static_premise` lemmas plus `vyper_to_abi_embedded_head_bound`.

#### Not to try
Do not manually expand `contractABITheory.enc_def` in these consumers except where an existing encoding lemma requires it; the existing `enc_*_static_premise` lemmas are the proof interface. Do not prove tuple length directly in the mutual theorem. Do not require `values_have_types` or source Vyper values in these lemmas; they are relation consumers only.

### C4.4.5.3: Prove sparse value-typing projection lemmas
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 20
- Work units: 2
- Rationale: These are small structural facts from `sparse_has_type_def`, `sparse_values_have_type_def`, and standard `ALOOKUP`/`MEM` behavior. They are needed only to align the sparse conversion induction.
- Dependencies: C4.4.5.1

#### Progress note
New sparse-specific helper replacing the unworkable length-indexed sparse IH.

#### Summary
- Convert public `sparse_has_type tv n sparse` into length-independent `sparse_values_have_type tv sparse`.
- Extract `value_has_type tv v` from `ALOOKUP sparse k = SOME v` under `sparse_values_have_type`.
- These lemmas allow the `vyper_to_abi_sparse` `SUC` case to use the recursive IH on the same sparse map.

#### Statement
```sml
Theorem sparse_has_type_values_have_type[local]:
  !tv n sparse.
    sparse_has_type tv n sparse ==> sparse_values_have_type tv sparse

Theorem sparse_values_have_type_ALOOKUP[local]:
  !tv sparse k v.
    sparse_values_have_type tv sparse /\ ALOOKUP sparse k = SOME v ==>
    value_has_type tv v
```

#### Approach
Prove `sparse_has_type_values_have_type` by induction on `sparse`, unfolding `value_has_type_def` only as needed for the recursive sparse predicate equations. For `ALOOKUP`, either use an existing `ALOOKUP_MEM` theorem if available or prove by induction on `sparse`; then apply `sparse_values_have_type_def`. Keep both lemmas local.

#### Not to try
Do not attempt to prove `sparse_has_type tv (SUC n) sparse ==> sparse_has_type tv n sparse`; it is false when the sparse map contains key `n`. Do not use sortedness or key bounds for this component; only value typing is needed.

### C4.4.5.4: Prove strengthened mutual Vyper-to-ABI conversion bound theorem
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: The proof follows the conversion recursion exactly and each branch now has a matching relation conclusion. Sparse recursion is de-risked by the length-independent sparse value predicate and default ABI bound helpers.
- Dependencies: C4.4.5.2, C4.4.5.3
- Checkpoint: yes

#### Progress note
This is the lynchpin replacement for the failed monolithic suffix in E0781.

#### Summary
- Use `ho_match_mp_tac vyper_to_abi_ind` with strengthened relation conclusions.
- First conjunct proves `abi_av_bound_rel` for successful single-value conversion.
- List conjunct proves `abi_av_list_bound_rel` for heterogeneous tuple/list conversion.
- Same and sparse conjuncts prove `EVERY abi_av_bound_rel` plus output length facts.
- Sparse branch uses `sparse_values_have_type`, `sparse_values_have_type_ALOOKUP`, and default ABI bounds for missing entries.

#### Statement
```sml
Theorem vyper_to_abi_bound_rel_strong[local]:
  (!tenv typ v av tv.
     vyper_to_abi tenv typ v = SOME av /\
     evaluate_type tenv typ = SOME tv /\
     value_has_type tv v ==>
     abi_av_bound_rel tenv typ tv av) /\
  (!tenv ts vs avs tvs.
     vyper_to_abi_list tenv ts vs = SOME avs /\
     LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
     values_have_types tvs vs ==>
     abi_av_list_bound_rel tenv ts avs tvs) /\
  (!tenv typ vs avs tv.
     vyper_to_abi_same tenv typ vs = SOME avs /\
     evaluate_type tenv typ = SOME tv /\
     all_have_type tv vs ==>
     EVERY (abi_av_bound_rel tenv typ tv) avs /\ LENGTH avs = LENGTH vs) /\
  (!tenv typ tv n sparse avs.
     vyper_to_abi_sparse tenv typ tv n sparse = SOME avs /\
     evaluate_type tenv typ = SOME tv /\
     sparse_values_have_type tv sparse ==>
     EVERY (abi_av_bound_rel tenv typ tv) avs /\ LENGTH avs = n)
```

#### Approach
Start with `ho_match_mp_tac vyper_to_abi_ind`, then simplify `vyper_to_abi_def`, `value_has_type_def`, `abi_av_bound_rel_def`, `abi_av_list_bound_rel_def`, `sparse_values_have_type_def`, `AllCaseEqs()`, and `PULL_EXISTS`. In the base-type branch, use existing `vyper_to_abi_base_enc_length_bound`. In tuple/list/struct branches, use the list relation IH plus `abi_av_list_tuple_bound` to establish the first-conjunct length bound; in dynamic/fixed array branches use same/sparse IHs plus `abi_avs_dyn_array_bound`/`abi_avs_fixed_array_bound` and the relevant `vyper_abi_size_bound_def` arithmetic.

For `vyper_to_abi_list`, combine the head single-value IH and tail list IH directly into `abi_av_list_bound_rel_def`. For `vyper_to_abi_same`, combine the head single-value IH and tail same IH into `EVERY` and length. For `vyper_to_abi_sparse (SUC n)`, use the recursive sparse IH first; if `ALOOKUP sparse n = SOME v`, get `value_has_type tv v` from `sparse_values_have_type_ALOOKUP` and apply the single-value IH to the explicit conversion; if no value exists, add the default ABI element using `default_to_abi_enc_length_bound` to prove `abi_av_bound_rel_def`.

#### Not to try
Do not make this theorem conclude the final exported four length bounds directly for every conjunct; that recreates the 13-goal monolith. Do not unfold tuple/array `enc` arithmetic inside the induction except through C4.4.5.2 boundary lemmas. Do not use the public sparse premise `sparse_has_type tv n sparse` in this strengthened theorem; use `sparse_values_have_type tv sparse`.

### C4.4.5.5: Derive exported `vyper_to_abi_enc_length_bound` from the strengthened theorem
- Kind: `compatibility_corollary`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: Once the strengthened theorem is proved, the current public four-conjunct theorem is a short wrapper selecting the right relation consumer for each conjunct.
- Dependencies: C4.4.5.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0781

#### Progress note
This closes the originally active C4.4.5 obligation without changing its external statement.

#### Summary
- Keep the current source statement of `vyper_to_abi_enc_length_bound` unchanged.
- Replace the failed proof body with a compatibility proof from `vyper_to_abi_bound_rel_strong`.
- Use `abi_av_bound_rel_def` for the single-value conjunct.
- Use tuple/same-array/fixed-array boundary lemmas for list, same, and sparse conjuncts.
- Convert public sparse typing to `sparse_values_have_type` via C4.4.5.3.

#### Statement
```sml
Theorem vyper_to_abi_enc_length_bound:
  (!tenv typ v av tv.
    vyper_to_abi tenv typ v = SOME av /\
    evaluate_type tenv typ = SOME tv /\
    value_has_type tv v ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    vyper_abi_size_bound tenv typ) /\
  (!tenv ts vs avs tvs.
    vyper_to_abi_list tenv ts vs = SOME avs /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
    values_have_types tvs vs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound_list tenv ts) /\
  (!tenv typ vs avs tv.
    vyper_to_abi_same tenv typ vs = SOME avs /\
    evaluate_type tenv typ = SOME tv /\
    all_have_type tv vs ==>
    LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    32 + LENGTH vs * vyper_abi_embedded_size tenv typ) /\
  (!tenv typ tv n sparse avs.
    vyper_to_abi_sparse tenv typ tv n sparse = SOME avs /\
    evaluate_type tenv typ = SOME tv /\
    sparse_has_type tv n sparse ==>
    LENGTH (enc (Array (SOME n) (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    n * vyper_abi_embedded_size tenv typ)
```

#### Approach
Prove the conjunctions independently. For the first, apply conjunct 1 of `vyper_to_abi_bound_rel_strong` and unfold `abi_av_bound_rel_def`. For the second, apply conjunct 2 then `abi_av_list_tuple_bound`. For the third, apply conjunct 3 then `abi_avs_dyn_array_bound`, rewriting `LENGTH avs = LENGTH vs`. For the fourth, derive `sparse_values_have_type` from `sparse_has_type`, apply conjunct 4, then use `abi_avs_fixed_array_bound` with `LENGTH avs = n`.

#### Not to try
Do not re-run `ho_match_mp_tac vyper_to_abi_ind` in this theorem; all induction belongs in C4.4.5.4. Do not leave the old `FAIL_TAC "probe_c44_vyper_to_abi_enc_length_bound"` or broad `TRY` suffix in place. Do not alter the theorem statement unless HOL reports a genuine falsehood after the strengthened local theorem is proved.

### C4.4.6: Discharge ABI encode resumes in `well_typed_type_builtin_success_type`
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 5
- Rationale: Builtin cases are low-risk only once the direct encoded-length theorem is available.
- Dependencies: C4.4.5
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: prior C4.4.6 plan

#### Progress note
Adds explicit dependency on C4.4.5 so builtin discharge waits for the direct encoded-length theorem.

#### Summary
Discharge builtin ABI encode proof resumes after C4.4.5. This should be the last ABI/builtin step in this local chain.

#### Approach
Use the direct encoded-length theorem exported by C4.4.5 in the finite builtin cases.

#### Not to try
Do not reopen ABI tuple/default algebra in builtin proof branches.

### C4.5: Close raw-call return well-formedness and Env/MsgGas support
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: After C4.4, the remaining builtin-file support is localized. `raw_call_return_type_well_formed` is arithmetic over `word_size`, `type_slot_size`, and the cases of `raw_call_return_type_def`; Env/MsgGas support is constructor-specific and should not require evaluator induction.
- Dependencies: C4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C4.5

#### Progress note
This leaf is no longer beginable before C4.4. Its dependency is intentional source-order scheduling: close the type-builtin success theorem first, then edit the later raw-call/Env support region.

#### Summary
- Remove the cheat in `raw_call_return_type_well_formed`.
- Audit/close the localized Env/MsgGas builtin support obligations reachable from `vyperSemanticsHolTheory`.
- Keep proofs in the builtin layer; do not duplicate evaluator/call case analysis.
- Use `word_size_le` and simple DIV/arithmetic facts for raw-call bounds.
- Checkpoint after `holbuild build vyperTypeBuiltinsTheory` succeeds and no C4.5 cheats remain.

#### Description
The raw-call theorem currently has a single cheated arithmetic subgoal after unfolding `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`. The proof should show the dynamic bytes return bound is well-formed under `flags.rcf_max_outsize < dimword(:256)`, using the already-proved `word_size_le` and the definition of `word_size`. Env/MsgGas issues mentioned in the task are part of the same builtin support layer; handle only those still reachable/cheated in current source.

#### Statement
Primary known source obligation:
```sml
Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
```
Also close any same-layer reachable Env/MsgGas support theorem(s) in `vyperTypeBuiltinsScript.sml` that still contain `cheat`/suspended proof text and are prerequisites for call/expression consumers.

#### Approach
First replace the raw-call cheat by strengthening the local arithmetic enough to prove all branches after case-splitting `flags`; keep any new helper near `word_size_le`. Expected shape: derive `word_size n ≤ n`, split on the branch that compares `word_size n < n`, and use the max-outsize/dimword hypothesis to discharge `type_slot_size`/well-formed natural-number bounds. Then grep/audit only `vyperTypeBuiltinsScript.sml` for remaining reachable Env/MsgGas cheats; close them by constructor rewriting using `env_item_type_def`/current context hypotheses, preserving any existing premise excluding `MsgGas` unless a checked theorem requires otherwise.

#### Not to try
Do not remove the `item <> MsgGas` premise from generic Env helper theorems just to make rewriting easier; the task notes this as a known issue, not permission to broaden a false helper. Do not start call-wrapper proofs under C5 from this leaf. Do not unfold the statement evaluator or raw-call expression evaluator here; consumers should use this well-formedness/support boundary.

### C5: Call wrapper soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Call wrappers are downstream consumers of completed expression/statement/builtin soundness and function signature consistency; no new evaluator induction is required.
- Required for completion: yes
- Dependencies: C2.8, C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: old C5

#### Progress note
C5 remains downstream; it must not be used by C2 internal-call proof.

#### Summary
- Prove call wrapper theorems in `vyperTypeCallSoundnessScript.sml`.
- External/special wrappers consume C2/C4 expression soundness.
- Internal no-TypeError and preservation wrappers consume completed statement/body soundness.
- No new evaluator induction or semantic case duplication.

#### Statement
Current source theorem names:
```sml
internal_call_no_type_error
internal_call_type_preservation
external_call_no_type_error
special_call_no_type_error
```

#### Approach
Prove wrappers as projections/corollaries. Use `functions_well_typed_body` or its repaired non-circular analogue, expression soundness for call expressions, and statement body soundness; avoid redoing call evaluator case analysis except for the one-step wrapper shape if current theorem statement is exactly an `eval_expr` call.

#### Not to try
Do not feed these wrappers back into `vyperTypeStmtSoundnessScript.sml`. Do not duplicate C2.7 call-frame proof internals unless a small projection helper is missing.

#### Argument
The call wrappers are API-facing corollaries of the completed mutual expression/statement soundness and function consistency facts. External and special calls reduce to the expression soundness of the corresponding call expressions. Internal calls use function signature/body typing to instantiate statement-list soundness for the callee body, then project no-TypeError or success preservation from the joint invariant. The wrappers preserve the frozen public behavior but are not proof drivers for the mutual theorem.

#### Definition design
The wrapper interface should expose the existing names `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error`. If a wrapper cannot be proved by projection, add a projection lemma from C2/C4 with the exact conclusion rather than unfolding evaluator internals here.

#### Code structure
Edit `semantics/prop/vyperTypeCallSoundnessScript.sml`. It may import completed `vyperTypeStmtSoundness` and `vyperTypeBuiltins`, but no earlier theory may import this file for C2 work.

### C5.1: External and special call no-TypeError wrappers
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These wrappers avoid internal function body recursion and reduce to completed expression/call-target facts.
- Progress transition: `refinement`
- Carries progress/evidence from: old C5.1

#### Progress note
Scheduled after C2/C4 through parent dependencies.

#### Summary
- Prove `external_call_no_type_error` and `special_call_no_type_error`.
- Consume C2 expression soundness and C4 raw/special-call boundary facts.
- Keep proofs as wrapper projections.

#### Statement
```sml
Theorem external_call_no_type_error: ...
Theorem special_call_no_type_error: ...
```

#### Approach
Instantiate the expression soundness theorem on the relevant `Call` expression and project `no_type_error_eval`. Use the target discriminating assumptions to select the external/special call case; any target-specific fact should already be in C4/C2.

#### Not to try
Do not unfold raw-call or builtin definitions here.

### C5.2: Internal call no-TypeError wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Existing function body typing and completed statement soundness supply internal-call no-TypeError; proof should be a projection from joint invariants.
- Dependencies: C5.1
- Progress transition: `refinement`
- Carries progress/evidence from: old C5.2

#### Progress note
Downstream wrapper only; does not affect C2.

#### Summary
- Prove `internal_call_no_type_error`.
- Use completed expression/internal-call mutual soundness and function consistency.
- Preserve current theorem statement unless source repair is needed and non-frozen.

#### Statement
```sml
Theorem internal_call_no_type_error: ...
```

#### Approach
Instantiate `eval_all_type_sound_mutual`/expression no-TypeError wrapper for `Call ty (IntCall (src,fn)) args drv`, or use the completed internal-call expression resume via a smaller expression theorem. Use `fn_sig_argument_bounds`/`functions_well_typed_body` only if the current wrapper statement requires explicit body facts.

#### Not to try
Do not redo the body evaluation proof; C2.7 owns it.

### C5.3: Internal call success preservation wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: This is the preservation projection counterpart to C5.2 and should reuse the same decomposition.
- Dependencies: C5.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C5.3

#### Progress note
Checkpoint because public wrappers depend on call preservation.

#### Summary
- Prove `internal_call_type_preservation`.
- Project state and expression result typing from completed joint soundness.
- Avoid fresh evaluator induction.

#### Statement
```sml
Theorem internal_call_type_preservation: ...
```

#### Approach
Use the same instantiated expression/call soundness theorem as C5.2, then specialize to the `INL` success result and project `state_well_typed` plus `expr_runtime_typed`. Add a small projection lemma if the joint theorem conclusion is inconvenient.

#### Not to try
Do not weaken the preservation conclusion or ignore account/env invariants if the current source theorem needs them downstream.

### C6: Public fresh soundness wrapper surface
- Kind: `proof_group`
- Risk: 2
- Work priority: 60
- Work units: 0
- Rationale: The frozen public behaviors are projections of the subsystem joint invariants once assignment/statement/call/builtin layers are cheat-free.
- Required for completion: yes
- Dependencies: C5.3, C3.3, C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: old C6

#### Progress note
C6 remains the public surface layer. It may adjust internal helper use but must keep wrappers equivalent in strength to the TASK list.

#### Summary
- Prove/repair public wrapper theorems in `vyperTypeSoundnessNewScript.sml`.
- Preserve frozen public behavior: no well-typed TypeError and preservation for success/exceptional results.
- Wrappers should be projections, not new evaluator inductions.
- Any missing projection indicates a C2/C5 helper gap to repair.

#### Statement
Public wrappers equivalent in strength to:
```sml
typed_stmts_no_type_error
typed_stmts_success_preserves_state_env
typed_stmts_exception_preserves_state_and_return_type
typed_expr_no_type_error
typed_expr_success_preserves_type
typed_callable_body_no_type_error
```

#### Approach
For each public wrapper, instantiate the strongest available joint theorem and simplify the result predicates. If a public theorem has a legacy statement shape, prove a stronger internal lemma and derive the legacy-compatible corollary.

#### Not to try
Do not weaken frozen public behavior. Do not start a parallel soundness induction in the public file.

#### Argument
Public soundness follows by instantiating the completed fresh-stack joint invariants for statements, expressions, callable bodies, assignment/call helpers, and projecting the user-facing conclusions. No public theorem should require new semantic case analysis: statement no-TypeError and preservation come from C2; expression no-TypeError/success typing from C2/C4; callable body no-TypeError from C5/C2 function body soundness; assignment/call wrappers from C1/C5.

#### Definition design
The public surface must expose wrappers equivalent in strength to `typed_stmts_no_type_error`, `typed_stmts_success_preserves_state_env`, `typed_stmts_exception_preserves_state_and_return_type`, `typed_expr_no_type_error`, `typed_expr_success_preserves_type`, and `typed_callable_body_no_type_error`. Internal theorem names/statements may be strengthened or renamed, but compatibility corollaries with these public names/strength must remain. Failure sign: a public wrapper proof unfolding evaluator definitions rather than projecting a completed joint theorem.

#### Code structure
Edit only the public fresh surface `semantics/prop/vyperTypeSoundnessNewScript.sml` and small projection lemmas in immediate prerequisite theories if necessary. Do not edit retired old theories unless C7 proves they are still imported.

### C6.1: Prove/repair the six public wrapper theorems
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: After subsystem theorems are complete, wrapper projection is standard; failures should expose only missing projection lemmas, not new architecture.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C6.1

#### Progress note
Scheduled after C5/C3/C4 through parent dependencies.

#### Summary
- Close all public wrapper cheats in `vyperTypeSoundnessNewScript.sml`.
- Preserve the six frozen public behaviors listed by the TASK.
- Use projection lemmas from C2/C5 rather than evaluator unfolding.
- Checkpoint before final full-stack validation.

#### Statement
Current source-authoritative public wrapper theorems corresponding to the six TASK names/behaviors.

#### Approach
Prove each wrapper by `drule`/`irule` against the relevant subsystem theorem and simplify definitions of public result predicates. If a theorem statement is awkward but non-frozen internally, add a stronger helper in the lower layer and keep the public wrapper equivalent in strength.

#### Not to try
Do not alter public theorem strength to avoid side conditions. Do not include old retired-stack theorems in the proof path.

### C7: Final `vyperSemanticsHolTheory` zero-CHEAT validation
- Kind: `validation`
- Risk: 1
- Work priority: 70
- Work units: 3
- Rationale: Mechanical final build/audit; any remaining warning gives concrete evidence for a small follow-up replan.
- Required for completion: yes
- Dependencies: C6.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C7

#### Progress note
Final completion criterion remains unchanged.

#### Summary
- Run `holbuild build vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.
- If warnings remain, identify the exact reachable theory/theorem and escalate for a focused component.
- Do not clean unrelated repository files as part of this validation.

#### Statement
```sh
holbuild build vyperSemanticsHolTheory
```
succeeds with zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.

#### Approach
Run the build exactly as the TASK requires and inspect CHEAT warnings. Use a scoped dependency/reachability audit to distinguish in-scope fresh-stack warnings from old retired theories; only escalate in-scope reachable obligations.

#### Not to try
Do not use direct HOL. Do not stage or modify untracked scratch files during validation.
