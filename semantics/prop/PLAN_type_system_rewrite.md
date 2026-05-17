# PLAN

## Structured Components

### C1: Finish assignment-target joint soundness in `vyperTypeStatePreservationScript.sml`
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The current source already contains the strengthened joint theorem statement, preservation side supplied by `assign_target_preserves_state_well_typed_mutual`, and many branch-local storage/hashmap/array helper lemmas. Remaining work is branch integration under the evaluator-recursion induction, not a new architecture.
- Required for completion: yes
- Progress transition: `replacement`
- Invalidates prior progress/evidence: prior PLAN C1-C1.3 slice-only scope

#### Progress note
This replaces the previous narrow slice-only structured plan because the TASK contract is the whole fresh type-system soundness stack. Current SML source and the 2026-05-13 handover make assignment-target soundness the first required path.

#### Summary
- Prove the currently suspended/cheated branches inside `assign_target_sound_mutual`.
- Do not weaken the theorem’s strengthened premises: `assignable_type`, `assign_operation_runtime_typed`, `assign_operation_matches_target_shape`, and `assign_target_assignable_context` stay in the statement.
- The first conjunct proves `runtime_consistent env cx st' ∧ no_type_error_result res` for `assign_target`; the second conjunct does the same for `assign_targets`.
- Preservation should be discharged uniformly from `assign_target_preserves_state_well_typed_mutual`; branch work focuses on ruling out `TypeError`.
- Completion checkpoint is `holbuild build vyperTypeStatePreservationTheory` with no CHEAT/suspend in this theory.

#### Description
This component covers exactly the five assignment-target obligations named in the TASK: `sound_TopLevelVar` HashMapRef case, `sound_TopLevelVar` ArrayRef case, `sound_ImmutableVar`, `sound_TupleTargetV`, and `sound_assign_targets_cons`. Helper lemmas already present around the `assign_target_sound_mutual` proof may be reused or tightened, but do not introduce a parallel no-TypeError theorem tree that duplicates evaluator recursion.

#### Statement
```sml
Theorem assign_target_sound_mutual:
  (!cx gv op st res st'.
    assign_target cx gv op st = (res, st') ==>
    !env tgt ty.
      runtime_consistent env cx st /\
      target_runtime_typed env cx st tgt ty gv /\
      assignable_type env.type_defs ty /\
      assign_operation_runtime_typed env ty op /\
      assign_operation_matches_target_shape gv op /\
      assign_target_assignable_context cx gv st ==>
      runtime_consistent env cx st' /\ no_type_error_result res) /\
  (!cx gvs vs st res st'.
    assign_targets cx gvs vs st = (res, st') ==>
    !env tgts.
      runtime_consistent env cx st /\
      target_assignment_values_assignable env cx st tgts gvs vs /\
      EVERY (\gv. assign_target_assignable_context cx gv st) gvs ==>
      runtime_consistent env cx st' /\ no_type_error_result res)
```

#### Approach
Use `ho_match_mp_tac assign_target_ind`, as in the source, and keep each semantic branch narrow. In every branch first split the preservation conjunct and solve it by the all-result preservation theorem; then expand `assign_target_def` or `assign_targets_def` only far enough to expose the failing TypeError branch and dispatch with an exact branch helper.

#### Not to try
Do not remove or weaken `assign_target_assignable_context`; statement-level proofs later depend on it. Do not start separate standalone `assign_target_*_no_type_error` inductions; compatibility wrappers belong after this joint theorem. Do not use broad `gvs[..., AllCaseEqs(), ...]` before isolating the semantic branch; this caused case explosion in the handover.

#### Argument
The mutual theorem follows the evaluator recursion for `assign_target`/`assign_targets`. The strengthened premises provide exactly what no-TypeError needs: `target_runtime_typed` identifies the location and typed leaf path; `assignable_type` rules out `NoneTV` leaves; `assign_operation_runtime_typed` proves the operation is accepted at the leaf; `assign_operation_matches_target_shape` prevents tuple/non-tuple shape mismatches; and `assign_target_assignable_context` supplies runtime writability/static lookup facts for scoped and top-level storage/hashmap locations. State/env/account preservation is already an all-result theorem, so no branch needs to reprove it. The remaining cases are semantic leaf cases: storage `HashMapRef`, storage `ArrayRef`, immutable assignment, tuple fan-out, and list sequencing. In all error branches, storage reads and layout/lookups either produce runtime errors or are ruled out by context; recursive subscript assignment TypeErrors are ruled out by `assign_subscripts_no_type_error_runtime_typed`; write-back TypeErrors are ruled out by typed-value write lemmas; and successful assignment results are ruled no-TypeError by `assign_result_no_type_error_from_successful_assign`.

#### Definition design
No new core definitions should be added in this component. The proof interface is a set of branch-local boundary lemmas that match evaluator branches: (1) a HashMapRef branch lemma consuming `split_hashmap_subscripts`, `compute_hashmap_slot`, final leaf type, and operation runtime typing; (2) ArrayRef branch lemmas for dynamic append, dynamic pop, and ordinary read/assign/write; (3) immutable update no-TypeError boundaries; (4) tuple/list projection lemmas for `target_assignment_values_assignable`. Failure signs: if the proof needs to unfold `compute_hashmap_slot` or `resolve_array_element` deeply inside `sound_TopLevelVar`, extract a branch lemma; if the tuple branch cannot call the `assign_targets` IH, strengthen the shape/assignability projection rather than destructing all targets inline.

#### Code structure
All assignment-target branch helpers and resumes belong in `semantics/prop/vyperTypeStatePreservationScript.sml`, immediately before or inside the `assign_target_sound_mutual` section. Keep low-level helpers `[local]` unless consumed by statement soundness. Export only the final mutual theorem and already-needed compatibility corollaries. Do not move static env-extension or scope-pop facts into this file; those remain in `vyperTypeEnvExtension`, `vyperTypeEnvPreservation`, and `vyperTypeScopePop`.

### C1.1: Integrate the TopLevelVar `HashMapRef` branch
- Kind: `proof`
- Risk: 2
- Rationale: The source already contains the required decomposition and branch helper names (`target_path_type_HashMapT_assign_target_decomp`, `target_path_type_HashMapT_split_leaf_runtime`, `assign_target_HashMapRef_branch_no_type_error`). Integration should be a branch-local application exercise.

#### Summary
- Close the `HashMapRef` subcase in `Resume assign_target_sound_mutual[sound_TopLevelVar]`.
- Use context assignability and target typing to obtain nonempty subscripts, hashmap declaration facts, slot lookup, split prefix, and final leaf typing.
- Use `assign_target_HashMapRef_branch_no_type_error` for all no-TypeError subbranches after semantic expansion.
- Preserve the existing successful storage `Value` branch proof unchanged.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_TopLevelVar]:
  ...
  (* HashMapRef case *)
```

#### Approach
In the `lookup_global ... = INL (HashMapRef ...)` branch, first derive module/declaration/slot facts from `assign_target_assignable_context` and the successful lookup. Then apply `target_path_type_HashMapT_assign_target_decomp` and `target_path_type_HashMapT_split_leaf_runtime` to produce the `split_hashmap_subscripts`, final leaf type, non-`NoneTV`, and well-formedness premises expected by `assign_target_HashMapRef_branch_no_type_error`.

#### Not to try
Do not inline `compute_hashmap_slot` proof obligations in the mutual proof. Do not destruct the whole declaration/lookup tree after the branch has already identified `HashMapRef`; use exact lookup/declaration lemmas to connect the branch to the context facts.

### C1.2: Integrate the TopLevelVar `ArrayRef` branch
- Kind: `proof`
- Risk: 2
- Rationale: The source contains focused ArrayRef lemmas for resolve-array errors, leaf typing, dynamic append/pop, and ordinary read/assign/write. The remaining work is selecting the right helper after splitting on operation and final type.
- Dependencies: C1.1

#### Summary
- Close the `ArrayRef` subcase in `sound_TopLevelVar`.
- Split into dynamic `AppendOp`, dynamic `PopOp`, and ordinary assignment/update/replace paths.
- For resolver errors use `resolve_array_element_error_not_TypeError`; for successful resolution use leaf-type/well-formedness helper facts.
- Delegate read/assign/write result branches to the local ArrayRef no-TypeError helpers.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_TopLevelVar]:
  ...
  (* ArrayRef case *)
```

#### Approach
After `lookup_global` returns `ArrayRef`, derive root `ArrayTV elem_tv bd` and use `resolve_array_element ... (REVERSE sbs)`. If resolver fails, show the error is not `TypeError`; if it succeeds, use `resolve_array_element_leaf_type_sc` and `resolve_array_element_well_formed_sc`. Then case split on `(op, final_tv)` and apply `assign_target_TopLevelVar_ArrayRef_AppendOp_dynamic_no_type_error`, `assign_target_TopLevelVar_ArrayRef_PopOp_dynamic_no_type_error`, `assign_target_ArrayRef_Replace_ordinary_ntr`, or `assign_target_ArrayRef_ordinary_ntr` as appropriate.

#### Not to try
Do not try to prove append/pop by the ordinary branch helper without checking the evaluator’s special dynamic-array arms. Do not unfold storage backend operations more than needed; `get_storage_backend_no_error`, typed write lemmas, and the branch helpers should hide those details.

### C1.3: Prove `sound_ImmutableVar` branch
- Kind: `proof`
- Risk: 2
- Rationale: Immutable assignment has no top-level layout/hashmap complications and existing preservation helpers (`set_immutable_preserves_*`) are already factored out. The branch is a standard expansion plus operation-runtime/assign-result no-TypeError argument.
- Dependencies: C1.1, C1.2

#### Summary
- Resume `assign_target_sound_mutual[sound_ImmutableVar]`.
- Use `assign_target_assignable_context_ImmutableVar` simplification and target runtime typing for the immutable location.
- Rule out assignment subscript TypeErrors via `assign_subscripts_no_type_error_runtime_typed` or the leaf operation lemma.
- Use immutable preservation helpers only for the preservation conjunct.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_ImmutableVar]:
  ...
```

#### Approach
Split preservation first using `cj 1 assign_target_preserves_state_well_typed_mutual`. For no-TypeError, expand the immutable `assign_target_def` branch; from `target_runtime_typed` obtain the immutable value type and `target_path_type`. Empty path uses `assign_operation_runtime_typed_leaf_no_type_error`; nonempty path uses `assign_subscripts_no_type_error_runtime_typed`, and successful writes close with `assign_result_no_type_error_from_successful_assign`.

#### Not to try
Do not treat immutable variables as scoped variables by rewriting locations away; the evaluator uses a distinct immutable setter path. Do not ignore the `assignable_type` premise, since it supplies the non-`NoneTV` side condition for recursive subscript assignment.

### C1.4: Prove `sound_TupleTargetV` branch
- Kind: `proof`
- Risk: 2
- Rationale: The strengthened shape predicate exists specifically to make tuple assignment safe, and the second mutual IH handles the recursive fan-out through `assign_targets`.
- Dependencies: C1.3

#### Summary
- Resume `assign_target_sound_mutual[sound_TupleTargetV]`.
- Show non-tuple operations are impossible or immediately no-TypeError by `assign_operation_matches_target_shape`.
- For `Replace` with a tuple value, convert `target_runtime_typed` and `value_has_type` information into `target_assignment_values_assignable`.
- Invoke the `assign_targets` IH for the fan-out evaluator call.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_TupleTargetV]:
  ...
```

#### Approach
Expand only the `TupleTargetV` branch of `assign_target_def`, then use `assign_operation_matches_target_shape_def` to force the operation/value shape required by tuple fan-out. From tuple target runtime typing and value typing, derive the list relation required by `target_assignment_values_assignable`; use the context premise’s `EVERY` projection and call the second conjunct IH on `assign_targets`.

#### Not to try
Do not destruct every subtarget manually. If the required list fact is not directly available, prove a small projection lemma from `target_runtime_typed` plus tuple `value_has_type` to `target_assignment_values_assignable` rather than doing case-by-case tuple recursion in the branch.

### C1.5: Prove `sound_assign_targets_cons` branch
- Kind: `proof`
- Risk: 2
- Rationale: This branch exactly matches the mutual recursion: first assign the head target, then recurse on the tail under the runtime consistency produced by the first IH.
- Dependencies: C1.4

#### Summary
- Resume `assign_target_sound_mutual[sound_assign_targets_cons]`.
- Project `target_assignment_values_assignable` into head target facts and tail list facts.
- Use head `assign_target` IH to preserve runtime consistency and no-TypeError.
- On head success, use tail `assign_targets` IH with updated state and projected `EVERY assign_target_assignable_context`.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_assign_targets_cons]:
  ...
```

#### Approach
Case split the head `assign_target` result. If it is an error, the head IH already gives no-TypeError and runtime consistency for the returned state. If it succeeds, use the all-result preservation/runtime consistency from the head IH as the precondition for the tail IH; destruct the list predicates only enough to expose head/tail conjuncts.

#### Not to try
Do not re-run `assign_target_def` for the head inside this branch; the induction hypothesis is the proof interface. Do not assume contexts are preserved automatically for the tail unless the definition of `assign_targets` really passes the original evaluated target values and the `EVERY` premise is projected correctly.

### C1.6: State-preservation build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical build and warning audit after C1.1-C1.5; no mathematical uncertainty remains once all resumes are completed.
- Dependencies: C1.5
- Checkpoint: yes

#### Summary
- Run `holbuild build vyperTypeStatePreservationTheory`.
- Confirm there are no `cheat`/unresolved `suspend` warnings in `vyperTypeStatePreservationScript.sml` reachable from this theory.
- Record exact remaining downstream failures/warnings before editing statement soundness.
- If this checkpoint reveals new state-preservation cheats in current source, escalate for plan augmentation before continuing.

#### Statement
```sh
holbuild build vyperTypeStatePreservationTheory
```

#### Approach
Use the build log as the source of truth. Grep the state-preservation script for `cheat` and unresolved `suspend` only after the theory builds, because stale comments or old retired theories are not obligations.

#### Not to try
Do not proceed to statement assignment cases if the strengthened assignment mutual theorem is still cheated; downstream statement proofs would be proving against an untrusted premise.

### C2: Finish statement/evaluator joint soundness in `vyperTypeStmtSoundnessScript.sml`
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The workhorse mutual theorem already follows `evaluate_ind` and states the desired joint invariant. Existing helper layers provide env extension, scope-pop, expression soundness, target typing, and assignment soundness; remaining cases are applications of those interfaces and the assignment side-condition bridges.
- Required for completion: yes
- Dependencies: C1

#### Summary
- Prove all suspended cases of `eval_all_type_sound_mutual` in the fresh statement soundness theory.
- Assignment branches must derive the strengthened assignment premises rather than weakening C1.
- Non-assignment statement, iterator, target, and expression cases should use the existing joint invariant and imported expression/builtin/call facts.
- This component is the main source of public wrappers for typed statements and expressions.
- Completion checkpoint is `holbuild build vyperTypeStmtSoundnessTheory` with no CHEAT/suspend in this theory.

#### Statement
```sml
Theorem eval_all_type_sound_mutual:
  (!cx s. ... type_stmt ... eval_stmt ... ==>
     state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
     case res of INL _ => env_consistent env' cx st'
               | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn) /\
  (!cx ss. ... type_stmts ... eval_stmts ... ==> ...) /\
  (!cx it. ... well_typed_iterator ... eval_iterator ... ==> ...) /\
  (!cx tgt. ... well_typed_atarget ... eval_target ... ==> ...) /\
  (!cx tgts. ... eval_targets ... ==> ...) /\
  (!cx bt. ... type_place_target ... eval_base_target ... ==> ...) /\
  (!cx tyv id body vs. ... eval_for ... ==> ...) /\
  (!cx e. ... well_typed_expr ... eval_expr ... ==> ...) /\
  (!cx es. ... well_typed_exprs ... eval_exprs ... ==> ...)
```

#### Approach
Keep the single `evaluate_ind` proof and resume individual cases. For any case that evaluates a subexpression/substatement/target first, apply the matching IH immediately to obtain state/env/account preservation, no-TypeError, and result typing, then feed those facts into the next evaluator call. Assignment cases depend on C1 plus the bridge lemmas in C2.1-C2.4.

#### Not to try
Do not split statement no-TypeError and preservation into separate theorems. Do not add ad hoc assumptions to assignment statement branches; derive them from `target_runtime_typed`, `target_values_runtime_typed`, `env_consistent`, `assignable_type`, and the typing rule. Do not prove target/evaluation cases by expanding expression evaluators when `vyperTypeExprSoundness` already exports the needed soundness.

#### Argument
The theorem is true by mutual induction on the evaluator recursion. Each evaluator clause either returns a trivial control result; evaluates subterms, where the IH supplies joint state/env/accounts/no-TypeError facts; or calls a lower soundness layer. Expression and target results are handled in the same induction because statement assignment needs evaluated target runtime typing in the same state in which assignment is performed. Assignment branches are the only strengthened call sites: after target evaluation and value evaluation/materialisation, target runtime typing plus env consistency yields `assign_target_assignable_context`, typing/value facts yield `assign_operation_runtime_typed`, and shape lemmas yield `assign_operation_matches_target_shape`; then C1 proves assignment no-TypeError and runtime consistency after all results. Scope blocks and loops use existing scope-pop/frame lemmas so successful block-local env extensions are popped back to the caller env on exits.

#### Definition design
The key local definition is already present: `assignment_value_static_assignable_context`, separating cx/static lookup facts from state-dependent assignability. Its proof interface must provide (1) static context from `target_runtime_typed`/`target_values_runtime_typed` and `env_consistent`; (2) full `assign_target_assignable_context`/`EVERY` context from static context plus runtime typed targets; and (3) direct corollaries from runtime typed targets. Failure signs: if assignment branches need to inspect top-level layout details directly, the bridge is too weak; if tuple assignment needs per-element context proofs in the statement case, strengthen the `target_values_runtime_typed` list bridge instead.

#### Code structure
All statement-level bridge lemmas and case resumes belong in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the existing C5.2/C5.4 comments and `eval_all_type_sound_mutual`. Do not move assignment-target branch helpers out of `vyperTypeStatePreservationScript.sml`; statement code should consume only the exported assignment theorem and statement-side bridge lemmas. Public wrappers remain in `vyperTypeSoundnessNewScript.sml`, not here, unless the current file already exports compatibility lemmas consumed by call soundness.

### C2.1: Audit/prove assignment assignable-context bridge lemmas
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: The current source already contains the intended definition and bridge lemmas; this component is an audit/carry-forward proof obligation, with only mechanical repair if names drift.
- Dependencies: C1.6
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: current source lines defining `assignment_value_static_assignable_context` and lemmas through `target_values_runtime_typed_imp_EVERY_assignable_context`

#### Progress note
Current source evidence shows these lemmas are present before `eval_all_type_sound_mutual`; the executor should verify they build and reuse them rather than designing new predicates.

#### Summary
- Ensure `assignment_value_static_assignable_context` and its direct simplification lemmas build.
- Ensure mutual/static/direct bridges from runtime typed targets to `assign_target_assignable_context` build.
- These lemmas are mandatory inputs for `AnnAssign`, `Assign`, and tuple/list assignment branches.
- If any bridge statement is too weak at a call site, strengthen here, not in the statement branch.

#### Statement
```sml
Definition assignment_value_static_assignable_context_def: ... End

Theorem target_runtime_typed_imp_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    env_consistent env cx st ==>
    assign_target_assignable_context cx gv st

Theorem target_values_runtime_typed_imp_EVERY_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    env_consistent env cx st ==>
    EVERY (\gv. assign_target_assignable_context cx gv st) gvs
```

#### Approach
Build the existing lemmas first. The single-target proof should use the mutual runtime-typed induction plus env-consistency projections for top-level storage/hashmap; the list proof is the second projection of the same mutual theorem.

#### Not to try
Do not derive top-level assignability from a successful assignment result in normal statement branches; failed assignments still need no-TypeError. The bridge must be available before assignment is executed.

### C2.10: Statement soundness build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical build and warning audit after statement cases are resumed.
- Dependencies: C2.6, C2.7, C2.8, C2.9
- Checkpoint: yes

#### Summary
- Run `holbuild build vyperTypeStmtSoundnessTheory`.
- Confirm no unresolved `cheat` or `suspend` remains in `vyperTypeStmtSoundnessScript.sml`.
- Record any remaining reachable warnings that now come only from builtin/call/final wrapper layers.
- Escalate if a statement case requires strengthening the mutual theorem rather than local helper lemmas.

#### Statement
```sh
holbuild build vyperTypeStmtSoundnessTheory
```

#### Approach
Use the build log and targeted grep. If failures show the theorem statement lacks a postcondition needed by multiple cases, stop and escalate rather than proving duplicate case-local facts.

#### Not to try
Do not mark statement cases complete while relying on cheated builtin/call theorem imports; final C6 audit must see zero reachable CHEAT warnings.

### C2.2: Assignment operation runtime/shape bridge lemmas for statement branches
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: Replace operations are already covered in current source; append/update require standard projections from typing and builtin/binop soundness. These lemmas are local consumers of existing assignment-operation definitions.
- Dependencies: C1.6
- Carries progress/evidence from: current `assign_operation_runtime_typed_Replace_from_value_has_type` and `assign_operation_matches_target_shape_Replace_from_typed` if present

#### Summary
- Prove/reuse `Replace` runtime-typed and shape lemmas from evaluated value typing.
- Prove append/pop/update shape facts needed by `Append` and `AugAssign` cases.
- For `AnnAssign`, use `assignable_type_evaluate_not_NoneTV` instead of local non-None cheats.
- These lemmas should unify directly with C1 premises.

#### Statement
Representative required outputs:
```sml
Theorem assign_operation_runtime_typed_Replace_from_value_has_type:
  !env ty tv v.
    evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v ==>
    assign_operation_runtime_typed env ty (Replace v)

Theorem assign_operation_matches_target_shape_Replace_from_typed:
  !env cx st tgt ty gv tv v.
    target_runtime_typed env cx st tgt ty gv /\
    evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v ==>
    assign_operation_matches_target_shape gv (Replace v)
```
Add analogous narrowly-scoped lemmas for the exact `AppendOp`, `PopOp`, and `Update` operations used by current statement cases if not already present.

#### Approach
For Replace, case split on `gv`; tuple cases use tuple value typing/list lengths, while base cases simplify the shape predicate. For Update/AugAssign, derive operation runtime typing from the typed binop/update-binop theorem and derive shape from the evaluated target shape; keep the lemma conclusion exactly matching the `assign_target_sound_mutual` premise.

#### Not to try
Do not hide update-binop no-TypeError failures by cheating these bridge lemmas; if the update operation needs builtin/binop proof support, depend on C4.1. Do not use `metis_tac` over the whole statement context when a two-premise operation bridge would make the branch stable.

### C2.3: Prove `AnnAssign` statement case
- Kind: `proof`
- Risk: 2
- Rationale: After C1 and C2.1-C2.2, the branch is a linear composition of target evaluation, expression/materialisation typing, assignment side conditions, and assignment soundness.
- Dependencies: C2.1, C2.2, C4.1

#### Summary
- Resume `eval_all_type_sound_mutual[AnnAssign]`.
- Derive target runtime typing from the target IH and value typing from expression/materialise soundness.
- Derive `assignable_type` and non-`NoneTV` side conditions from the typing rule.
- Call C1 with `Replace v`, operation runtime typing, shape, and assignable context.

#### Statement
```sml
Resume eval_all_type_sound_mutual[AnnAssign]:
  ...
```

#### Approach
Apply IHs in evaluator order and thread the updated state/env facts. Use the typing rule to expose the annotated type, `assignable_type`, and `evaluate_type`; apply materialisation/value typing if the evaluator materialises a top-level value. Then use C2.1 and C2.2 to supply the strengthened assignment premises and conclude with `cj 1 assign_target_sound_mutual`.

#### Not to try
Do not resurrect old `ty <> NoneT` local cheats; the source has `assignable_type` exactly for this branch. Do not call assignment soundness before converting successful target evaluation into `target_runtime_typed` in the post-target state.

### C2.4: Prove `Assign` statement case including tuple/list assignment
- Kind: `proof`
- Risk: 2
- Rationale: The branch uses the list conjuncts of the evaluator IH and the second conjunct of C1. The handover explicitly identifies `target_assignment_values_assignable` as the required interface.
- Dependencies: C2.1, C2.2

#### Summary
- Resume `eval_all_type_sound_mutual[Assign]`.
- For single-target Replace, use the same bridge pattern as `AnnAssign`.
- For tuple/list assignment, produce `target_assignment_values_assignable env cx st tgts gvs vs`.
- Use `target_values_runtime_typed_imp_EVERY_assignable_context` for the `EVERY` context side condition.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Assign]:
  ...
```

#### Approach
Separate the evaluator’s single-target and multiple-target paths. In the tuple/list path, use the target-list IH for `LIST_REL3 target_runtime_typed`, expression-list IH for expression result typing, and the typing rule’s assignability facts to establish `target_assignment_values_assignable`; then call `cj 2 assign_target_sound_mutual`.

#### Not to try
Do not assign tuple elements by repeated single-target reasoning in the statement proof. The executor should make the list predicate fit the second assignment theorem rather than duplicating `assign_targets` recursion.

### C2.5: Prove `AugAssign` statement case
- Kind: `proof`
- Risk: 2
- Rationale: This is the only assignment branch coupled to update-binop/builtin no-TypeError facts; after C4.1 it follows the same target/value/operation/context pattern as Replace.
- Dependencies: C2.1, C2.2, C4.1

#### Summary
- Resume `eval_all_type_sound_mutual[AugAssign]`.
- Use target evaluation to obtain current target runtime typing and assignable context.
- Use expression soundness plus update-binop typing to form the `Update` assignment operation premise.
- Call the first conjunct of C1 and thread its runtime consistency result.

#### Statement
```sml
Resume eval_all_type_sound_mutual[AugAssign]:
  ...
```

#### Approach
Follow evaluator order: target IH, expression IH, update/binop evaluation, then assignment. The update operation premise should be supplied by a bridge lemma depending on `well_typed_update_binop_no_type_error`/runtime typing; shape comes from the evaluated target value shape.

#### Not to try
Do not prove update-binop arithmetic/string/bytes cases inside `AugAssign`; those belong in C4.1. Do not weaken the branch to no-TypeError only, because successful update must still preserve state/env/account invariants via runtime consistency.

### C2.6: Prove non-assignment statement control/result cases
- Kind: `proof_batch`
- Risk: 2
- Rationale: These are standard evaluator cases with no new definitions: Pass/Continue/Break/Raise/Assert/Return/Log/Expr use direct simplification or expression IHs.
- Dependencies: C2.1

#### Summary
- Resume cases: `Pass`, `Continue`, `Break`, `Return_NONE`, `Return_SOME`, `RaiseBare`, `RaiseUnreachable`, `RaiseReason`, `AssertBare`, `AssertUnreachable`, `AssertReason`, `Log`, and `Expr`.
- Return-with-value uses expression soundness and `return_exception_typed`.
- Assertions/logging use expression IHs and no-control/no-TypeError facts.
- Successful simple statements preserve the current or typed environment by simplification.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Pass]: ...
...
Resume eval_all_type_sound_mutual[Expr]: ...
```

#### Approach
For literal control statements, unfold the corresponding evaluator and typing definitions and simplify `stmt_error_ok_def`/`return_exception_typed_def`. For cases evaluating expressions, invoke the expression IH first, destruct the result, and use the no-control lemmas for exceptional expression results.

#### Not to try
Do not inspect expression evaluator internals in statement cases. Do not over-generalize these into new global theorems unless the same two-line proof repeats with brittle tactic code.

### C2.7: Prove structured statement/list/loop/iterator cases
- Kind: `proof_batch`
- Risk: 2
- Rationale: The required frame and scope-pop infrastructure is already imported and proved; cases follow evaluator recursion and existing scope-bracket helpers.
- Dependencies: C2.3, C2.4, C2.5

#### Summary
- Resume cases: `If`, `For`, `Stmts_nil`, `Stmts_cons`, `For_nil`, `For_cons`, `Iterator_Array`, and `Iterator_Range`.
- Use statement/list/for IHs in evaluator order.
- Use `scope_bracket_post`, `scope_bracket_preserves`, and env-extension lemmas for pushed scopes.
- Iterator success must return values typed by the iterator element type.

#### Statement
```sml
Resume eval_all_type_sound_mutual[If]: ...
Resume eval_all_type_sound_mutual[For]: ...
Resume eval_all_type_sound_mutual[Stmts_nil]: ...
Resume eval_all_type_sound_mutual[Stmts_cons]: ...
Resume eval_all_type_sound_mutual[For_nil]: ...
Resume eval_all_type_sound_mutual[For_cons]: ...
Resume eval_all_type_sound_mutual[Iterator_Array]: ...
Resume eval_all_type_sound_mutual[Iterator_Range]: ...
```

#### Approach
For sequence cases, destruct the first result and apply the next IH only in the success branch; in exception branches preserve the appropriate env-extension witness. For scoped bodies/loops, use the existing scope bracket decomposition and pop preservation lemmas instead of re-proving scope list invariants.

#### Not to try
Do not manually reason about `scopes` length except through the scope-pop helper layer. Do not force loop success to produce the extended body env at the caller; the theorem statement intentionally restores caller env consistency.

### C2.8: Prove target and base-target evaluation cases
- Kind: `proof_batch`
- Risk: 2
- Rationale: These cases are within the same mutual theorem precisely to supply assignment branches; the target/path typing helpers in expression soundness and state preservation already expose the required runtime target facts.
- Dependencies: C2.1

#### Summary
- Resume cases: `Target_Base`, `Target_Tuple`, `Targets_nil`, `Targets_cons`, `BaseTarget_Name`, `BaseTarget_BareGlobal`, `BaseTarget_TopLevel`, `BaseTarget_Subscript`, and `BaseTarget_Attribute`.
- Successful target cases must return `target_runtime_typed` or `LIST_REL3 target_runtime_typed`.
- Successful base-target cases must return `base_target_value_shape`, location runtime typing, and `target_path_type`.
- Use existing path/place bridge lemmas for subscript and attribute extensions.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Target_Base]: ...
...
Resume eval_all_type_sound_mutual[BaseTarget_Attribute]: ...
```

#### Approach
For base targets, apply expression/base-target IHs for subexpressions, then use the static `type_place_target`/`subscript_vtype`/`attribute_type` lemmas to extend `target_path_type`. For target tuples and target lists, use structural list reasoning and the mutual IH to build the `LIST_REL3` result.

#### Not to try
Do not prove top-level storage/hashmap lookup assignability here; this case only proves target runtime typing. Full assignment context is derived by C2.1 when an assignment statement consumes the target value.

### C2.9: Prove expression and expression-list delegated cases inside the statement mutual theorem
- Kind: `proof_batch`
- Risk: 2
- Rationale: Expression soundness is already a separate imported layer with the correct result typing (`expr_result_typed`); statement mutual expression cases should be wrappers around that layer.
- Dependencies: C4, C5

#### Summary
- Resume expression cases still suspended in `eval_all_type_sound_mutual`: names, literals, struct literals, subscripts, attributes, builtins, type builtins, pop, internal/external calls, and expression lists.
- Delegate builtin cases to C4 and call cases to C5.
- Preserve `expr_result_typed`, including the HashMapRef/place invariant.
- Expression-list cases use list IH and `exprs_runtime_typed` constructors.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Name]: ...
...
Resume eval_all_type_sound_mutual[Expr_Call_IntCall]: ...
Resume eval_all_type_sound_mutual[Exprs_* / eval_exprs cases]: ...
```

#### Approach
Use the exported expression soundness/no-TypeError/preservation theorems where available; otherwise, apply the expression IH in evaluator order and reconstruct `expr_result_typed_def`. Builtin and call expression cases should not unfold those subsystems after C4/C5 export their wrappers.

#### Not to try
Do not reintroduce the retired `expr_runtime_typed_hashmap_ref_place` theorem; the current architecture uses `expr_result_typed`. Do not unfold builtin/call evaluators in this mutual proof beyond the call to their soundness theorem.

### C3: Audit/prove assignment compatibility wrappers in `vyperTypeAssignSoundnessScript.sml`
- Kind: `compatibility_wrappers`
- Risk: 1
- Rationale: Current grep did not show cheats in `vyperTypeAssignSoundnessScript.sml`; the task still names these wrappers as in-scope if reachable, so this is an audit/reuse component rather than new architecture.
- Required for completion: yes
- Dependencies: C1
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: current `vyperTypeAssignSoundnessScript.sml` theorem names

#### Progress note
If current source already proves the wrappers without cheats, carry them forward. If build reveals a hidden dependency on the old no-TypeError architecture, reprove them as corollaries of C1 rather than by a second induction.

#### Summary
- Verify or reprove `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error`.
- They are compatibility corollaries only; internal proofs should use C1 directly.
- If proofs are needed, instantiate C1 with the operation-specific runtime/shape/context premises and project `no_type_error_result`.
- Completion is `holbuild build vyperTypeAssignSoundnessTheory` with no CHEAT warnings.

#### Statement
```sml
Theorem assign_target_no_type_error: ...
Theorem assign_target_update_no_type_error: ...
Theorem assign_target_append_no_type_error: ...
```

#### Approach
First build/audit the current file. If a wrapper is cheated or broken, prove it by applying `cj 1 assign_target_sound_mutual` to the relevant `assign_target` evaluation and then simplifying `no_type_error_result_def`; operation-specific premises should come from the assignment operation bridge lemmas, not from unfolding evaluator internals.

#### Not to try
Do not restore standalone recursive proofs for these wrappers. Do not strengthen public wrapper statements unless callers require it; the stronger theorem is C1.

### C4: Finish builtin/binop/type-builtin no-TypeError layer in `vyperTypeBuiltinsScript.sml`
- Kind: `proof_subtree`
- Risk: 3
- Rationale: Derived from child component C4.2 risk 3. "ecrecover_no_type_error list destruct: after Cases_on vs >> gvs[LIST_REL_CONS1] for 4-element lists, auto-generated variable names for tails are unpredictable. Need EL-index approach (LIST_REL_EL_EQN) or single-pass value-destruct approach (Cases_on vs >> Cases_on h >> simp, like BuiltinTyping file pattern) instead of trying to predict gvs-generated tail names."
- Required for completion: yes
- Supersedes: prior PLAN C1, prior PLAN C1.1, prior PLAN C1.2, prior PLAN C1.3
- Progress transition: `replacement`

#### Progress note
The previous structured plan for `slice_no_type_error` is now reclassified as one builtin subcase under this broader task-required builtin layer. Any already proved slice helper can be carried forward by C4.3.

#### Summary
- Prove `well_typed_binop_no_type_error`, `well_typed_update_binop_no_type_error`, and the assignment-subscript update path lemmas named in the TASK.
- Prove the remaining suspended/cheated cases in `well_typed_builtin_app_no_type_error` and type-builtin no-TypeError theorems.
- Keep builtin fixes localized unless a checked probe shows an evaluator/typing mismatch.
- Export only the dispatcher theorems consumed by expression/statement soundness.
- Completion is `holbuild build vyperTypeBuiltinsTheory` with no CHEAT/suspend warnings.

#### Statement
Required outputs include:
```sml
Theorem well_typed_binop_no_type_error: ...
Theorem well_typed_update_binop_no_type_error: ...
Theorem assign_subscripts_update_leaf_no_type_error: ...
Theorem assign_operation_runtime_typed_leaf_no_type_error: ...
Theorem assign_subscripts_no_type_error_runtime_typed: ...
Theorem assign_subscripts_preserves_type_runtime_typed: ...
Theorem well_typed_builtin_app_no_type_error: ...
Theorem well_typed_type_builtin_app_no_type_error: ...
```

#### Approach
Prove evaluator-level boundary lemmas for each builtin constructor, then make the dispatcher theorem a case split over the typing derivation/builtin constructor. For update-binop, prove the binop no-TypeError theorem first and derive the update path lemmas from it so assignment does not duplicate binop cases.

#### Not to try
Do not unfold all ABI/bytes/crypto arithmetic in the global dispatcher; isolate it in per-builtin boundary lemmas. Do not patch `AugAssign` or assignment-subscript lemmas with local cheats if `well_typed_update_binop_no_type_error` is missing. Do not change public semantics for Env/MsgGas without a small probe showing the current theorem cannot match current evaluator behavior.

#### Argument
Builtin soundness is a finite case analysis over executable builtin/type-builtin typing. Static typing fixes arity and evaluated argument type values; `LIST_REL value_has_type` fixes the runtime value constructors accepted by the evaluator. Each builtin branch must show the evaluator may return a normal value or runtime error but not `Error (TypeError msg)`. Binops provide the key reusable boundary for update assignment: once a typed binop cannot produce TypeError and successful results have the expected type, `Update` leaf assignment and recursive subscript assignment inherit no-TypeError and preservation. ABI, bytes, crypto, env/account, and type-builtin cases should be hidden behind branch lemmas matching the evaluator call, so statement/expression soundness only consumes the final well-typed builtin theorem.

#### Definition design
No broad new builtin framework is required. Use small boundary lemmas named after evaluator operations, e.g. typed slice/evaluate_slice no-TypeError, ABI encode/decode no-TypeError under typed arguments and slot-size bounds, Env/Acc field no-TypeError under context well-typedness, and binop constructor lemmas. A definition change is permitted only if a branch probe proves the executable typing accepts a case the evaluator treats as TypeError (or vice versa); then repair the executable typing/runtime locally and update the branch theorem. Failure signs: dispatcher proof still needs to split byte representations or ABI internals; branch lemma too weak. A branch theorem needs statement env facts; builtin theorem statement is missing a necessary context well-typed premise.

#### Code structure
All work belongs in `semantics/prop/vyperTypeBuiltinsScript.sml`. Keep per-constructor helpers `[local]` unless imported by state preservation (the update-subscript path may need exported lemmas). Do not edit `vyperBuiltinTypingScript.sml` unless current fresh `vyperTypeBuiltinsScript.sml` imports and depends on it for the failing theorem. If an executable typing/runtime mismatch is checked, make the minimal local repair in the corresponding typing/evaluator theory and document it in the theorem comment.

### C4.1: Prove binop and update-binop no-TypeError path
- Kind: `proof_batch`
- Risk: 2
- Rationale: The file already enumerates local binop no-TypeError lemmas for arithmetic/comparison/boolean/flag/string/bytes/address cases. The dispatcher and update wrappers should be finite case analysis plus reuse.
- Checkpoint: yes

#### Summary
- Prove `well_typed_binop_no_type_error` from the per-binop local lemmas.
- Prove `well_typed_update_binop_no_type_error` from the binop theorem and update typing shape.
- Close inherited assignment-update path lemmas: `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`.
- This checkpoint unblocks `AugAssign` and assignment Array/HashMap branches that call recursive subscript assignment.

#### Statement
```sml
Theorem well_typed_binop_no_type_error: ...
Theorem well_typed_update_binop_no_type_error: ...
Theorem assign_subscripts_update_leaf_no_type_error: ...
Theorem assign_operation_runtime_typed_leaf_no_type_error: ...
Theorem assign_subscripts_no_type_error_runtime_typed: ...
Theorem assign_subscripts_preserves_type_runtime_typed: ...
```

#### Approach
Case split on the binary operator and the typing rule/type values; each leaf should match an existing `binop_no_type_error_*` lemma. For recursive `assign_subscripts`, use the function induction/structural path induction already aligned with the definitions, with update leaf delegated to `well_typed_update_binop_no_type_error`.

#### Not to try
Do not prove recursive subscript no-TypeError by unfolding binop cases at every recursive leaf. Do not leave `assign_subscripts_preserves_type_runtime_typed` depending on a cheated update leaf; C1’s storage write proofs rely on the type preservation conclusion.

### C4.2: Prove ECRecover no-TypeError theorem using a runtime-argument boundary and robust list extraction
- Kind: `proof_subtree`
- Risk: 2
- Rationale: Prior episodes proved the hard ECRecover boundary facts; the remaining failure is proof engineering around four-element list decomposition. Splitting runtime ECRecover safety from static/list extraction removes the fragile auto-generated-tail-name dependency, so all children are standard list/type reasoning.
- Progress transition: `refinement`
- Carries progress/evidence from: E0158, E0159, E0160

#### Progress note
This refines the previously stuck C4.2 obligation after E0160. The mathematical route is unchanged, but the brittle in-line list destruct is replaced by two explicit local helpers: one for runtime ECRecover safety, one for extracting the four typed runtime arguments from the theorem assumptions.

#### Summary
- Close the local theorem `ecrecover_no_type_error` exactly as stated in the user task/source.
- Reuse existing/proved converter and `evaluate_ecrecover` boundary lemmas from the current source.
- Add a small runtime-shape lemma for `[hash; v; r; s]`, independent of `ts`/`tvs` list plumbing.
- Add a list-extraction lemma deriving that runtime shape from `LENGTH ts = 4`, `HD ts`, `EVERY (TL ts)`, `MAP evaluate_type`, and `LIST_REL value_has_type`.
- The final theorem becomes one `irule`/`metis_tac` step plus `evaluate_builtin_def`, not a long fragile destruct proof.

#### Description
This subtree is limited to the ECRecover no-TypeError proof in `semantics/prop/vyperTypeBuiltinsScript.sml`. It should not re-plan the rest of C4 or other builtin branches. The previous stuck point was not a false theorem; it was a fragile proof that destructed `vs` and then referred to auto-generated names such as `t'`/`t''` after `gvs[LIST_REL_CONS1]`. The replacement structure isolates all four-list reasoning in a dedicated helper whose conclusion directly matches a runtime safety lemma.

#### Argument
ECRecover can return a `TypeError` only when the builtin wrapper sees the wrong argument shape/type or when `evaluate_ecrecover` rejects one of the four runtime arguments. Under the theorem hypotheses, `ty = BaseT AddressT` and `LENGTH ts = 4`; `LIST_REL` plus the `MAP evaluate_type` equality imply `vs` also has length 4 and each runtime argument has the evaluated type of the corresponding static argument. The first static argument is exactly `BaseT (BytesT (Fixed 32))`, so its runtime value has type `BaseTV (BytesT (Fixed 32))`, hence is a `BytesV` of length 32. Each of the remaining three static arguments is either `BaseT (UintT 256)` or `BaseT (BytesT (Fixed 32))`; either runtime type makes `ecrecover_arg_to_num` return `SOME`. Therefore the call reduces to `evaluate_ecrecover [BytesV hash_bytes; v_arg; r_arg; s_arg]` with all non-TypeError side conditions satisfied.

#### Definition design
No new semantic definition is needed. The proof interface should be local theorems only:

1. Converter boundary facts: `value_has_type (BaseTV (UintT 256)) v` and `value_has_type (BaseTV (BytesT (Fixed 32))) v` each imply `ecrecover_arg_to_num v ≠ NONE`.
2. `evaluate_ecrecover_no_type_error`: a 32-byte hash plus three non-`NONE` converter results implies `evaluate_ecrecover [BytesV hash_bytes; v_arg; r_arg; s_arg] ≠ INR (TypeError msg)`.
3. Runtime builtin boundary: four runtime values with the ECRecover runtime typing pattern imply `evaluate_builtin cx acc (BaseT AddressT) ECRecover [v0;v1;v2;v3] ≠ INR (TypeError msg)`.
4. Static/list extraction: the theorem hypotheses imply the existence of `v0 v1 v2 v3` such that `vs = [v0;v1;v2;v3]` and those four runtime typing predicates hold.

Failure sign: if the extraction lemma requires knowing exact post-`gvs` names for tails, abandon that tactic and switch to the EL-index proof described in the child component.

#### Code structure
Make all changes in `semantics/prop/vyperTypeBuiltinsScript.sml`, immediately around the existing ECRecover helper block before `Theorem ecrecover_no_type_error[local]`. Keep the helper theorems `[local]`. Do not edit library files and do not introduce an SML proof utility. Preserve the current theorem statement for `ecrecover_no_type_error`; replace only its proof body and add local helper theorems above it if needed.

### C4.2.1: Carry forward ECRecover converter and evaluate_ecrecover boundary lemmas
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: These lemmas already appear in the current source and prior episodes report them proved; they are direct case splits on values/converters and `evaluate_ecrecover_def`.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0158, E0159

#### Progress note
Carry forward the already-proved local lemmas at lines 1511-1539 of `vyperTypeBuiltinsScript.sml`. The executor should only adjust them if later edits accidentally break names or statements.

#### Summary
- Reuse the existing `ecrecover_arg_Uint256_not_none` and `ecrecover_arg_BytesT32_not_none` lemmas.
- Reuse the existing `evaluate_ecrecover_no_type_error` lemma.
- These are the semantic boundary facts that make the main theorem independent of ECRecover internals.
- No new proof search should be spent here unless the file no longer contains these exact local theorems.

#### Statement
```sml
Theorem ecrecover_arg_Uint256_not_none[local]:
  !v. value_has_type (BaseTV (UintT 256)) v ⇒ ecrecover_arg_to_num v ≠ NONE

Theorem ecrecover_arg_BytesT32_not_none[local]:
  !v. value_has_type (BaseTV (BytesT (Fixed 32))) v ⇒ ecrecover_arg_to_num v ≠ NONE

Theorem evaluate_ecrecover_no_type_error[local]:
  !hash_bytes v_arg r_arg s_arg msg.
    LENGTH hash_bytes = 32 ∧
    ecrecover_arg_to_num v_arg ≠ NONE ∧
    ecrecover_arg_to_num r_arg ≠ NONE ∧
    ecrecover_arg_to_num s_arg ≠ NONE ⇒
    evaluate_ecrecover [BytesV hash_bytes; v_arg; r_arg; s_arg] ≠ INR (TypeError msg)
```

#### Approach
The converter lemmas are by `Cases_on v` and simplification with `value_has_type_def` and `ecrecover_arg_to_num_def`. The `evaluate_ecrecover` lemma is by case-splitting the three converter calls and rewriting `evaluate_ecrecover_def`; the non-`NONE` hypotheses discharge the bad cases.

#### Not to try
Do not strengthen these lemmas to mention `well_typed_builtin_app` or static `ts`; that reintroduces the list plumbing into the semantic boundary. Do not inline `evaluate_ecrecover_def` in the final theorem when this boundary lemma can be applied.

### C4.2.2: Runtime ECRecover argument pattern prevents builtin TypeError
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: This is a small wrapper over already-proved boundary facts plus one case split on the first runtime value. It avoids the final theorem having to unfold all ECRecover internals.
- Dependencies: C4.2.1
- Carries progress/evidence from: E0159

#### Progress note
This helper packages the boundary facts that E0159 identified as necessary. It is new in the plan, but directly supported by the proved converter/evaluator lemmas from the prior attempts.

#### Summary
- Prove a local lemma about a concrete four-element runtime argument list.
- The first argument must have type `BaseTV (BytesT (Fixed 32))`.
- Each of the last three arguments may have either `BaseTV (UintT 256)` or `BaseTV (BytesT (Fixed 32))`.
- The conclusion is directly about `evaluate_builtin ... ECRecover [v0;v1;v2;v3]`, so the final theorem need only produce these four values and predicates.

#### Statement
```sml
Theorem ecrecover_runtime_args_no_type_error[local]:
  !cx acc v0 v1 v2 v3 msg.
    value_has_type (BaseTV (BytesT (Fixed 32))) v0 ∧
    (value_has_type (BaseTV (UintT 256)) v1 ∨ value_has_type (BaseTV (BytesT (Fixed 32))) v1) ∧
    (value_has_type (BaseTV (UintT 256)) v2 ∨ value_has_type (BaseTV (BytesT (Fixed 32))) v2) ∧
    (value_has_type (BaseTV (UintT 256)) v3 ∨ value_has_type (BaseTV (BytesT (Fixed 32))) v3) ⇒
    evaluate_builtin cx acc (BaseT AddressT) ECRecover [v0; v1; v2; v3] ≠ INR (TypeError msg)
```

#### Approach
First derive from the last-three disjunctions that `ecrecover_arg_to_num v1`, `v2`, and `v3` are non-`NONE` using the two converter lemmas. Then use `vht_BaseTV_BytesT_Fixed` or a direct `Cases_on v0` with `value_has_type_def` to get `v0 = BytesV hash_bytes` and `LENGTH hash_bytes = 32`. Finish by rewriting `evaluate_builtin_def` for `ECRecover` and applying `evaluate_ecrecover_no_type_error`.

#### Not to try
Do not destruct `ts`, `tvs`, or `vs` in this lemma; it should know nothing about static argument lists. Do not use `gvs` in a way that consumes the `value_has_type` hypotheses before the converter lemmas are applied; if simplification is too aggressive, use `fs` or explicitly exclude the relevant `vht_*` rewrites.

### C4.2.3: Extract ECRecover runtime argument typing from the theorem list hypotheses
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: The statement isolates the only previously fragile part. It is standard list-index reasoning from `LENGTH`, `MAP`, `EVERY`, and `LIST_REL`; using EL-index reasoning or disciplined destruct with immediate renaming avoids the known tail-name problem.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0160

#### Progress note
This checkpoint directly addresses E0160's stuck list destruct. Completion of this lemma confirms that the final theorem no longer depends on unpredictable `gvs`-generated tail variable names.

#### Summary
- From the main theorem assumptions, prove `vs` is exactly a four-element list.
- Extract runtime values `v0 v1 v2 v3` and their ECRecover-specific typing predicates.
- Use `MAP (evaluate_type ...) ts = MAP SOME tvs` to identify the runtime type at each position.
- Use `HD ts` for index 0 and `EVERY ... (TL ts)` for indices 1, 2, and 3.
- This lemma is the checkpoint replacing the failed in-line proof.

#### Statement
```sml
Theorem ecrecover_args_typed_from_lists[local]:
  !cx ts tvs vs.
    LENGTH ts = 4 ∧
    HD ts = BaseT (BytesT (Fixed 32)) ∧
    EVERY (λt. t = BaseT (UintT 256) ∨ t = BaseT (BytesT (Fixed 32))) (TL ts) ∧
    MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
    LIST_REL value_has_type tvs vs ⇒
    ?v0 v1 v2 v3.
      vs = [v0; v1; v2; v3] ∧
      value_has_type (BaseTV (BytesT (Fixed 32))) v0 ∧
      (value_has_type (BaseTV (UintT 256)) v1 ∨ value_has_type (BaseTV (BytesT (Fixed 32))) v1) ∧
      (value_has_type (BaseTV (UintT 256)) v2 ∨ value_has_type (BaseTV (BytesT (Fixed 32))) v2) ∧
      (value_has_type (BaseTV (UintT 256)) v3 ∨ value_has_type (BaseTV (BytesT (Fixed 32))) v3)
```

#### Approach
Preferred proof: derive `LENGTH tvs = 4` from the `MAP` equality and `LENGTH vs = 4` from `LIST_REL_LENGTH`; instantiate the witnesses as `EL 0 vs`, `EL 1 vs`, `EL 2 vs`, `EL 3 vs`, and use `LIST_REL_EL_EQN`, `EL_MAP`, and `EVERY_EL` to prove each predicate. For each static type equality, apply `evaluate_type_BaseT_SOME` to turn `evaluate_type ... (BaseT b) = SOME tv_i` into `tv_i = BaseTV b`. If EL lemmas are awkward in HOL4, a fallback is fixed-length destruct of `ts`, `tvs`, and `vs`, but immediately `rename1` each list tail/value after every split and use `fs/simp`, not `gvs`, for `LIST_REL_CONS1`.

#### Not to try
Do not repeat the failed pattern `Cases_on vs >> gvs[LIST_REL_CONS1] >> Cases_on t >> ... >> Cases_on t''`; the generated names are unstable. Do not expand `evaluate_builtin_def` here. Do not try to prove a version that concludes raw constructors like `UintV`/`BytesV` for the last three arguments; the disjunctive static typing is intentionally abstracted by `value_has_type`.

### C4.2.4: Prove the exact ecrecover_no_type_error theorem
- Kind: `proof`
- Risk: 1
- Rationale: After C4.2.2 and C4.2.3, the exact theorem is an immediate composition: extract the four runtime arguments, substitute `ty = BaseT AddressT`, and apply the runtime ECRecover safety lemma.
- Dependencies: C4.2.2, C4.2.3
- Progress transition: `refinement`
- Carries progress/evidence from: E0160

#### Progress note
This replaces only the brittle proof body of the existing local theorem. The theorem statement remains exactly the user-provided/source statement.

#### Summary
- Keep the theorem statement exact.
- Strip assumptions and use `ecrecover_args_typed_from_lists` to obtain `vs = [v0;v1;v2;v3]` plus runtime typing.
- Rewrite `ty` to `BaseT AddressT`.
- Apply `ecrecover_runtime_args_no_type_error`.
- Avoid direct four-level list destruct in this final proof.

#### Statement
```sml
Theorem ecrecover_no_type_error[local]:
  LENGTH ts = 4 ∧ ty = BaseT AddressT ∧
  HD ts = BaseT (BytesT (Fixed 32)) ∧
  EVERY (λt. t = BaseT (UintT 256) ∨ t = BaseT (BytesT (Fixed 32))) (TL ts) ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty ECRecover vs ≠ INR (TypeError msg)
```

#### Approach
Use the extraction lemma with the assumptions excluding `ty`, destruct the existential witnesses, and simplify with `ty = BaseT AddressT` and `vs = [v0;v1;v2;v3]`. Then `irule ecrecover_runtime_args_no_type_error` or `metis_tac` with the four runtime typing facts. This proof should not unfold `well_typed_builtin_app_def`; the caller already supplies the normalized ECRecover typing assumptions.

#### Not to try
Do not use `gvs[evaluate_builtin_def]` at the start of this theorem, because it can destroy the `≠ INR (TypeError msg)` goal and consume useful hypotheses. Do not rely on variable names produced by simplification of `LIST_REL_CONS1`; all list work belongs in C4.2.3.

### C4.3: Prove ABI encode/decode and tuple encoding builtin branches
- Kind: `proof_batch`
- Risk: 2
- Rationale: The TASK calls out ABI encode bound issues as localized. They should be solved by exact size/bound lemmas or a minimal typing-side bound repair if a probe shows the current premise is insufficient.

#### Summary
- Close suspended cases `abi_decode`, `abi_encode`, `encode_tuple`, and `encode_tuple_nowrap` in the builtin dispatcher.
- Prove local ABI evaluator no-TypeError lemmas under the typed argument and bound premises actually generated by executable typing.
- If a bound premise is missing, add a checked probe demonstrating the mismatch, then repair the internal typing/helper statement locally.
- Do not let ABI arithmetic leak into statement/expression soundness.

#### Statement
```sml
Resume well_typed_builtin_app_no_type_error[abi_decode]: ...
Resume well_typed_builtin_app_no_type_error[abi_encode]: ...
Resume well_typed_builtin_app_no_type_error[encode_tuple]: ...
Resume well_typed_builtin_app_no_type_error[encode_tuple_nowrap]: ...
```

#### Approach
First isolate the exact evaluator call after arity/type-list simplification. Prove a boundary lemma whose hypotheses are exactly the typing-derived size/bound facts and `value_has_type` premises; use ABI helper theorems from `vyperTypeABI` where available.

#### Not to try
Do not weaken the final no-TypeError theorem by excluding ABI cases. Do not add arbitrary numeric assumptions to dispatcher theorem statements unless they are derivable from executable typing or a repaired typing rule.

### C4.4: Prove Env/Acc and remaining simple builtin branches
- Kind: `proof_batch`
- Risk: 2
- Rationale: Most remaining builtins are finite projections from `context_well_typed`, account typing, or simple value constructors. The known MsgGas issue is handled by a probe-before-repair discipline inside this localized component.

#### Summary
- Close Env, Acc, block/blob hash, method id, crypto, arithmetic utility, make-array, ceil/floor, and other simple suspended builtin cases.
- For `Env MsgGas`, first inspect whether current executable typing and evaluator agree on a non-TypeError result.
- If they agree, prove the branch from context well-typedness; if not, make the minimal internal typing/runtime repair allowed by the TASK.
- Keep each constructor branch in a local helper when simplification is not one-line.

#### Statement
```sml
Resume well_typed_builtin_app_no_type_error[Env]: ...
Resume well_typed_builtin_app_no_type_error[Acc]: ...
(* plus remaining constructor cases listed by current suspends in vyperTypeBuiltinsScript.sml *)
```

#### Approach
For projection builtins, unfold the relevant evaluator branch and use the `context_well_typed`/`accounts_well_typed` field invariant. For constructors, prove the returned value has the expected type and observe no TypeError branch exists. For MsgGas, perform the smallest concrete evaluation/typing probe before choosing proof or repair.

#### Not to try
Do not silently skip MsgGas by making the branch unreachable unless executable typing actually rejects it. Do not change public frozen behavior; only internal helper/typing/runtime alignment is permitted.

### C4.5: Prove type-builtin no-TypeError dispatcher
- Kind: `proof_batch`
- Risk: 2
- Rationale: Type-builtin cases are finite and self-contained once conversions/defaults/ABI helpers are available.
- Dependencies: C4.2, C4.3, C4.4

#### Summary
- Prove remaining cheats in `well_typed_type_builtin_app_no_type_error` or equivalent current theorem.
- Use conversion/default/ABI helper theories rather than statement proof facts.
- Ensure all successful returned values are compatible with expression result typing consumers.
- Keep local branch helpers for conversion operations with nontrivial runtime checks.

#### Statement
```sml
Theorem well_typed_type_builtin_app_no_type_error: ...
```

#### Approach
Case split on the type-builtin constructor and the evaluated type value. For conversions, use existing conversion typing/no-TypeError lemmas; for defaults or constructors, unfold the evaluator and simplify with value typing facts.

#### Not to try
Do not merge type-builtin cases into ordinary builtin dispatcher if current source keeps them separate. Do not unfold conversion internals in expression soundness.

### C4.6: Builtin theory build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical build and warning audit after all builtin branch components.
- Dependencies: C4.1, C4.5
- Checkpoint: yes

#### Summary
- Run `holbuild build vyperTypeBuiltinsTheory`.
- Confirm no CHEAT or unresolved suspend remains in `vyperTypeBuiltinsScript.sml`.
- Confirm update-binop exported lemmas no longer inherit cheats.
- Escalate with concrete counterexample/probe output if a builtin typing/runtime mismatch remains.

#### Statement
```sh
holbuild build vyperTypeBuiltinsTheory
```

#### Approach
Use build output and grep. Any remaining builtin issue should be localized to a named constructor before downstream theories are rebuilt.

#### Not to try
Do not proceed to final semantic build with builtin CHEAT warnings, even if statement/call theories build through them.

### C5: Prove call soundness wrappers in `vyperTypeCallSoundnessScript.sml`
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The task lists four call wrappers. They should be corollaries of statement/body soundness plus function/context typing, not a second evaluator recursion. Current file has only the named cheated wrappers by grep.
- Required for completion: yes
- Dependencies: C2, C4

#### Summary
- Prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error`.
- Use the joint statement/body soundness theorem from C2 for internal callable bodies.
- Use builtin/external-call runtime boundary facts for external/special calls.
- Keep wrappers split only for the public/fresh surface; internally prove strongest joint facts where current source permits.
- Completion is `holbuild build vyperTypeCallSoundnessTheory` with no CHEAT warnings.

#### Statement
```sml
Theorem internal_call_no_type_error: ...
Theorem internal_call_type_preservation: ...
Theorem external_call_no_type_error: ...
Theorem special_call_no_type_error: ...
```

#### Approach
For internal calls, unfold call setup just enough to connect argument/default typing and function body typing to `eval_all_type_sound_mutual`; then project no-TypeError or preservation. For external/special calls, use context/account/runtime typing and imported builtin/expression facts to rule out TypeError in the evaluator branch.

#### Not to try
Do not duplicate statement evaluator induction inside call wrappers. Do not prove no-TypeError and preservation by two unrelated scripts if a joint internal-call lemma is needed; prove the joint lemma once and derive wrappers.

#### Argument
Calls enter the same typed execution world as statements: arguments/defaults produce typed values, local scope setup preserves state/env/account invariants, the callable body is typed under an extended environment, and body evaluation is covered by C2. Therefore internal-call no-TypeError and preservation are projections of a joint body-call invariant. External and special calls do not execute Vyper statements but are finite evaluator branches constrained by context/account typing and builtin-like runtime checks; their no-TypeError properties are localized boundary lemmas. The final public wrappers can remain split because callers/users expect those names, but proof work should flow through the joint invariant.

#### Definition design
Introduce a local joint internal-call lemma only if current wrappers cannot both be one-line projections from existing statement soundness. Its conclusion should include no-TypeError, state/account/env preservation, and return value typing/exception typing. Boundary probes: verify argument binding/default materialisation preserves `env_consistent`; verify body `ReturnException` values match declared return type via `return_exception_typed`. Failure signs: wrappers independently unfold the same call setup; extract a joint lemma.

#### Code structure
All call-specific lemmas belong in `semantics/prop/vyperTypeCallSoundnessScript.sml`. Do not move statement soundness wrappers into this file; import/consume `vyperTypeStmtSoundness`. If a helper is purely about default arguments or ABI conversion and already has a dedicated theory, keep the proof there only when the call file cannot prove it locally.

### C5.1: Joint internal-call body soundness lemma
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: The call wrappers need the same setup facts; a joint lemma avoids duplicate proof and follows the strongest-joint-invariant requirement.
- Dependencies: C2.10

#### Summary
- Prove a local joint lemma for well-typed internal callable body evaluation if not already present.
- Include no-TypeError, state/account/env preservation, and return type/exception typing.
- Use C2’s statement-list/body theorem after argument/default/local-scope setup.
- Derive both internal call wrappers from this lemma.

#### Statement
Use current source’s internal-call parameters. Desired conclusion shape:
```sml
... eval_internal_call ... = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  (* success value or ReturnException has declared return type; env/frame invariant preserved *)
  ...
```

#### Approach
Unfold internal-call setup to the point where a typed body is evaluated under an extended env/scope. Apply C2 statement soundness to the body, then use scope-pop/env-frame lemmas to restore caller invariants and convert body return exceptions to call results.

#### Not to try
Do not choose a lemma conclusion that only proves no-TypeError; `internal_call_type_preservation` would then repeat the same setup proof.

### C5.2: Derive internal call wrappers
- Kind: `compatibility_wrappers`
- Risk: 1
- Rationale: Once C5.1 exists, these are projections and simplifications.
- Dependencies: C5.1

#### Summary
- Prove `internal_call_no_type_error`.
- Prove `internal_call_type_preservation`.
- Keep theorem names/statements compatible with current callers.
- Avoid unfolding body evaluation again.

#### Statement
```sml
Theorem internal_call_no_type_error: ...
Theorem internal_call_type_preservation: ...
```

#### Approach
Apply the joint internal-call lemma to the evaluation equation and project `no_type_error_result`, state/env/account preservation, and result typing according to the wrapper statement.

#### Not to try
Do not edit public wrapper strength downward; the TASK freezes equivalent public behavior.

### C5.3: Prove external and special call no-TypeError wrappers
- Kind: `proof_batch`
- Risk: 2
- Rationale: These are finite call-entry branches, not evaluator-recursive statement proofs. They depend on context/account/builtin boundary facts already in the fresh stack.
- Dependencies: C4.6

#### Summary
- Prove `external_call_no_type_error`.
- Prove `special_call_no_type_error`.
- Use context/account well-typedness and ABI/builtin no-TypeError facts from C4.
- Keep any ABI encoding/decoding TypeError reasoning in C4 helpers.

#### Statement
```sml
Theorem external_call_no_type_error: ...
Theorem special_call_no_type_error: ...
```

#### Approach
Unfold only the top-level external/special call branch and dispatch ABI/builtin subcalls with C4 theorems. Runtime failures such as missing account or revert are allowed only as non-TypeError errors; use existing state/account invariants to rule out TypeError branches.

#### Not to try
Do not pull ABI encode bound arithmetic into this file. Do not assume all external failures are impossible; prove only that errors are not `TypeError` and that preserved invariants hold when the wrapper requires them.

### C5.4: Call theory build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical build and warning audit after call wrappers.
- Dependencies: C5.2, C5.3
- Checkpoint: yes

#### Summary
- Run `holbuild build vyperTypeCallSoundnessTheory`.
- Confirm no CHEAT remains in `vyperTypeCallSoundnessScript.sml`.
- Confirm wrappers are available to `vyperTypeSoundnessNewScript.sml` without changing public behavior.
- Escalate if a wrapper statement is stronger than current executable semantics with checked evidence.

#### Statement
```sh
holbuild build vyperTypeCallSoundnessTheory
```

#### Approach
Use the build log and grep. If a wrapper proof fails because of statement/body theorem shape, revisit C5.1 rather than patching wrappers independently.

#### Not to try
Do not claim final public soundness while call wrappers still depend on cheats.

### C6: Final public wrappers and reachable zero-CHEAT build
- Kind: `final_integration`
- Risk: 2
- Rationale: After C1-C5, the remaining work is compatibility projection in `vyperTypeSoundnessNewScript.sml` and a reachable build/audit. The task freezes wrapper strength but current source already exposes the named surface.
- Required for completion: yes
- Dependencies: C2, C3, C4, C5
- Checkpoint: yes

#### Summary
- Ensure `vyperTypeSoundnessNewScript.sml` exposes wrappers equivalent in strength to the six public obligations named in the TASK.
- Reprove/update wrappers only as projections of C2/C5/C4 joint theorems.
- Run `holbuild build vyperSemanticsHolTheory`.
- Audit the reachable dependency closure for zero CHEAT warnings.
- This is the final completion criterion.

#### Statement
Public wrapper surface must include equivalents of:
```sml
typed_stmts_no_type_error
typed_stmts_success_preserves_state_env
typed_stmts_exception_preserves_state_and_return_type
typed_expr_no_type_error
typed_expr_success_preserves_type
typed_callable_body_no_type_error
```
Final command:
```sh
holbuild build vyperSemanticsHolTheory
```

#### Approach
Use the strongest joint theorems as sources and project no-TypeError/preservation/return typing into the public wrapper statements. Then run the final aggregate build and inspect warnings from the reachable fresh stack only, excluding retired old theories unless still imported.

#### Not to try
Do not weaken the public wrappers; their behavior is frozen by the TASK. Do not count repository-wide unrelated cheats outside the reachable `vyperSemanticsHolTheory` closure as blockers, but do record any still-reachable old retired theory import as a task issue.

#### Argument
The public wrappers are corollaries of the joint soundness stack: statement wrappers come from C2’s mutual theorem; expression wrappers come from the expression components inside C2 and imported expression soundness; callable-body wrappers come from C5’s joint internal-call/body lemma. Since C1, C3, and C4 remove the lower-layer cheats used by those theorems, `vyperSemanticsHolTheory` can import the fresh final surface without reachable CHEAT warnings.

#### Definition design
No new public definitions should be introduced. If a wrapper needs a small compatibility predicate conversion (e.g. `stmt_error_ok` to no-TypeError plus return typing), prove it locally as a theorem, not as a new semantic definition. Failure sign: a public wrapper needs a stronger postcondition than C2/C5 exposes; strengthen the corresponding joint theorem rather than adding a second proof tree.

#### Code structure
Wrapper projections belong in `semantics/prop/vyperTypeSoundnessNewScript.sml`. The final aggregator `vyperSemanticsHolScript.sml` should continue importing the fresh final theory. Build/audit scripts or grep commands are not committed unless the repository already uses them for proof maintenance.
