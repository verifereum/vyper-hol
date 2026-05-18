# PLAN

## Structured Components

### C0: Confirm reachable fresh-stack proof frontier
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical holbuild/grep audit requested by the task handover; it does not require mathematical design and only records the exact current frontier before editing.
- Checkpoint: yes

#### Progress note
This is an executable audit checkpoint added to keep the PLAN task-scoped against current source. It does not replace any proof component; if it reveals extra reachable cheats in the named fresh theories, escalate for plan augmentation before broad cleanup.

#### Summary
- Run the current fresh-stack builds enough to identify the actual reachable CHEAT/suspend frontier.
- Start with `vyperTypeStatePreservationTheory`, then later use `vyperSemanticsHolTheory` for final reachability.
- Grep only the in-scope fresh theories listed in the TASK, not retired old theories.
- Treat current SML theorem statements as authoritative except for the frozen public behavior in the TASK.

#### Statement
```sh
holbuild build vyperTypeStatePreservationTheory
holbuild build vyperSemanticsHolTheory   # may fail/warn initially; record reachable fresh-stack cheats only
```

#### Approach
Use build logs plus targeted grep for `cheat`, `suspend`, and `CHEAT` in the fresh-stack theories. This checkpoint should not trigger edits by itself except to select the next already-planned component.

#### Not to try
Do not chase retired `vyperTypeSoundnessDefs/Helpers/Soundness` obligations unless the build proves they are still imported by `vyperSemanticsHolTheory`. Do not declare a theorem false from inspection alone; create a probe/escalation if a mismatch appears.

### C1: Finish assignment-target joint soundness in `vyperTypeStatePreservationScript.sml`
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The strengthened theorem and most branch-local helpers already exist in current source. The remaining named branches are finite evaluator branches under the existing mutual induction; risk is standard proof integration, not architectural uncertainty.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C1, TYPE_SYSTEM_REWRITE_PLAN.md assignment target update

#### Progress note
Carries forward the focused handover scope: `TopLevelVar` HashMapRef/ArrayRef, `ImmutableVar`, `TupleTargetV`, and `assign_targets_cons`. The theorem must keep the strengthened side conditions named in the TASK.

#### Summary
- Prove the five remaining branches of `assign_target_sound_mutual` in `vyperTypeStatePreservationScript.sml`.
- Do not weaken `assignable_type`, `assign_operation_runtime_typed`, `assign_operation_matches_target_shape`, or `assign_target_assignable_context` premises.
- Use the existing all-result preservation theorem for the runtime-consistency/state part; branch work is mainly no-TypeError.
- Complete with a state-preservation build/audit checkpoint before statement soundness uses the theorem.

#### Description
This component covers exactly the TASK’s focused state-preservation obligations: `sound_TopLevelVar` HashMapRef, `sound_TopLevelVar` ArrayRef, `sound_ImmutableVar`, `sound_TupleTargetV`, and `sound_assign_targets_cons`. Helpers may be added locally when a semantic branch needs a precise boundary lemma, but do not start a second assignment no-TypeError induction.

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
Use the existing `assign_target_ind`/resume structure. In each branch, first split off preservation and solve it with `assign_target_preserves_state_well_typed_mutual`, then expand only the semantic branch needed to expose impossible `TypeError` cases and discharge them with exact branch helpers.

#### Not to try
Do not use a broad `gvs[..., AllCaseEqs(), ...]` before isolating the branch; the handover identifies this as the cause of case explosion. Do not replace the joint theorem with legacy wrapper proofs or remove strengthened side conditions.

#### Argument
The mutual theorem follows the recursion of `assign_target` and `assign_targets`. `target_runtime_typed` identifies the runtime location and leaf path; `assignable_type` excludes `None` leaves; `assign_operation_runtime_typed` proves the leaf operation is accepted; `assign_operation_matches_target_shape` prevents tuple/non-tuple operation mismatches; and `assign_target_assignable_context` supplies writability/static lookup facts for scoped variables, storage, hashmaps, arrays, and immutables. The preservation half is already provided all-result by the state-preservation theorem, so the open proof obligations are only to rule out `TypeError` in the remaining branches. Storage/hashmap/array branches reduce to lookup/layout/subscript/write boundary lemmas; tuple assignment reduces to the second mutual conjunct; list sequencing reduces to head IH then tail IH under the updated runtime consistency.

#### Definition design
No new core definitions should be introduced here. The proof interface should be branch-local boundary lemmas matching evaluator branches: HashMapRef branch consumes split subscripts, computed slot, leaf typing, and operation typing; ArrayRef branch separates resolver failure, append, pop, and ordinary assign/update; ImmutableVar branch consumes immutable target typing plus subscript/leaf operation facts; TupleTargetV consumes shape and list assignment facts. Failure signs: needing to unfold storage backend, `compute_hashmap_slot`, or array resolution deeply inside the mutual proof means a local boundary lemma is missing.

#### Code structure
All helpers and resumes for this component belong in `semantics/prop/vyperTypeStatePreservationScript.sml`, near the `assign_target_sound_mutual` section. Keep branch helpers `[local]` unless statement soundness must import them. Do not move env-extension, env-preservation, or scope-pop facts into this file.

### C1.1: Close `TopLevelVar` HashMapRef branch
- Kind: `proof`
- Risk: 2
- Rationale: The handover names existing decomposition/leaf helper facts for this exact branch; remaining work is applying them at the resumed branch.
- Dependencies: C0
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C1.1

#### Progress note
Continue from the existing resumed `sound_TopLevelVar` proof; preserve the already-completed storage `Value` subcase.

#### Summary
- Close the `HashMapRef` subcase in `sound_TopLevelVar`.
- Derive hashmap declaration, nonempty subscripts, slot, split-prefix, and final leaf typing facts from target typing and assignable context.
- Apply the local HashMapRef no-TypeError branch lemma.
- Keep the proof branch-local.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_TopLevelVar]:
  ... (* HashMapRef case *)
```

#### Approach
After the successful `lookup_global = INL (HashMapRef ...)` split, derive module/declaration/slot facts from `assign_target_assignable_context`. Use the target-path decomposition lemmas to obtain the leaf type and split-subscript premises required by `assign_target_HashMapRef_branch_no_type_error`.

#### Not to try
Do not inline `compute_hashmap_slot` or redo declaration lookup reasoning after the branch is identified. Do not destruct unrelated storage `Value` subcases again.

### C1.2: Close `TopLevelVar` ArrayRef branch
- Kind: `proof`
- Risk: 2
- Rationale: ArrayRef proof is finite once resolver error/success and append/pop/ordinary operation branches are separated; current source already contains focused branch lemmas by handover.
- Dependencies: C1.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C1.2

#### Progress note
Uses existing ArrayRef helper layer where present; if a helper is missing, add the narrow local lemma instead of expanding storage backend internals.

#### Summary
- Close the `ArrayRef` subcase in `sound_TopLevelVar`.
- Split resolver failure from resolver success.
- In success, handle dynamic append, dynamic pop, and ordinary assign/update/write separately.
- Use existing typed resolver and write-back no-TypeError boundary lemmas.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_TopLevelVar]:
  ... (* ArrayRef case *)
```

#### Approach
From `ArrayRef`, obtain the root array value/type and call-site path. If `resolve_array_element` fails, use the resolver error-not-TypeError lemma. If it succeeds, combine leaf typing/well-formedness with operation/runtime typing and dispatch to the append, pop, or ordinary ArrayRef branch helper.

#### Not to try
Do not prove dynamic append/pop through the ordinary branch helper; the evaluator has special dynamic-array arms. Do not unfold storage backend operations if a typed write/helper lemma applies.

### C1.3: Close `ImmutableVar` branch
- Kind: `proof`
- Risk: 2
- Rationale: Immutable assignment has simpler lookup/layout structure; subscript and leaf operation no-TypeError lemmas already provide the hard recursion boundary.
- Dependencies: C1.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C1.3

#### Progress note
Continue the existing suspended `sound_ImmutableVar` proof.

#### Summary
- Resume `sound_ImmutableVar`.
- Use immutable target runtime typing to obtain leaf/path typing.
- Rule out leaf and recursive subscript TypeErrors through assignment-operation/subscript lemmas.
- Use immutable setter preservation only for the preservation conjunct.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_ImmutableVar]:
  ...
```

#### Approach
Split preservation first. For no-TypeError, expand the immutable evaluator branch, distinguish empty from nonempty path, and apply `assign_operation_runtime_typed_leaf_no_type_error` or `assign_subscripts_no_type_error_runtime_typed`; successful writes close by the generic assign-result no-TypeError lemma.

#### Not to try
Do not rewrite immutable variables into scoped variables; the evaluator uses a separate immutable setter path. Do not ignore `assignable_type`, because it provides non-`None` side conditions for recursive subscript assignment.

### C1.4: Close `TupleTargetV` branch
- Kind: `proof`
- Risk: 2
- Rationale: The strengthened shape predicate and second mutual conjunct are designed for this branch; any missing list projection is a small local lemma.
- Dependencies: C1.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C1.4

#### Progress note
Do not manually expand each subtarget; make the list predicate fit `assign_targets`.

#### Summary
- Resume `sound_TupleTargetV`.
- Use `assign_operation_matches_target_shape` to force the tuple `Replace` shape.
- Convert tuple target/value typing into `target_assignment_values_assignable`.
- Invoke the `assign_targets` mutual IH.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_TupleTargetV]:
  ...
```

#### Approach
Unfold only the tuple-target evaluator branch. From tuple runtime target typing and tuple value typing, derive the list relation required by `target_assignment_values_assignable`, project the `EVERY assign_target_assignable_context` premise, and apply the second mutual IH.

#### Not to try
Do not destruct every tuple element inside the statement branch. If the needed list fact is absent, prove a projection lemma from tuple `target_runtime_typed` plus `value_has_type`, not a case-by-case proof in the resume.

### C1.5: Close `assign_targets_cons` branch
- Kind: `proof`
- Risk: 2
- Rationale: This branch follows the mutual recursion exactly: head assignment then tail assignment under the head IH’s runtime consistency.
- Dependencies: C1.4
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C1.5

#### Progress note
Uses the mutual IH as the abstraction boundary for head assignment.

#### Summary
- Resume `sound_assign_targets_cons`.
- Project head and tail facts from `target_assignment_values_assignable` and `EVERY`.
- Apply head `assign_target` IH; if head errors, no-TypeError is already known.
- If head succeeds, apply tail `assign_targets` IH in the updated state.

#### Statement
```sml
Resume assign_target_sound_mutual[sound_assign_targets_cons]:
  ...
```

#### Approach
Split on the head assignment result. In the success branch, use the head IH’s `runtime_consistent env cx st'` as the precondition for the tail IH and use list-predicate projections for the tail assignability facts.

#### Not to try
Do not unfold `assign_target_def` for the head inside this branch. Do not assume assignable context is state-invariant unless the projected theorem/premise establishes exactly what the tail IH needs.

### C1.6: State-preservation build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical verification once all state-preservation resumes are completed.
- Dependencies: C1.5
- Checkpoint: yes

#### Progress note
This checkpoint gates downstream statement proof work on a non-cheated assignment-target theorem in the state-preservation theory.

#### Summary
- Build `vyperTypeStatePreservationTheory`.
- Confirm no `cheat` or unresolved `suspend` remains in `vyperTypeStatePreservationScript.sml`.
- Record any remaining warnings from imported theories separately.
- Escalate if new state-preservation cheats are found.

#### Statement
```sh
holbuild build vyperTypeStatePreservationTheory
```

#### Approach
Use the build log as source of truth, then targeted grep for active `cheat`/`suspend` in the file. Imported builtin warnings are handled by C4, not by altering C1.

#### Not to try
Do not proceed to statement assignment cases while `assign_target_sound_mutual` is still suspended or cheated.

### C2: Finish statement/evaluator joint soundness in `vyperTypeStmtSoundnessScript.sml`
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The theorem architecture is already the required strongest joint invariant following evaluator recursion. Remaining work is case resumption and assignment side-condition bridging using C1 and C4 outputs.
- Required for completion: yes
- Dependencies: C1, C4
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2

#### Progress note
Carries forward the existing plan’s statement-soundness structure. Assignment branches must be repaired for the strengthened assignment premises; do not weaken C1.

#### Summary
- Prove all remaining suspended/cheated cases in `eval_all_type_sound_mutual`.
- Assignment cases must derive `assign_operation_matches_target_shape` and `assign_target_assignable_context`.
- Non-assignment cases should use the mutual IH, expression/builtin/call boundaries, and scope/frame helper layers.
- This component supplies the statement/expression wrapper facts consumed by call and final soundness.

#### Statement
```sml
Theorem eval_all_type_sound_mutual:
  (* current source statement over eval_stmt/eval_stmts/eval_target/eval_expr/... *)
```

#### Approach
Continue the single evaluator mutual induction. In each evaluator case, apply sub-IHs in execution order, thread runtime consistency/state/env/account facts, and call lower-layer soundness theorems instead of unfolding their evaluators.

#### Not to try
Do not split no-TypeError and preservation into parallel proof trees. Do not add assumptions to assignment statement theorem statements; derive them from typing, target runtime typing, value typing, env consistency, and C2 bridge lemmas.

#### Argument
Statement soundness is by mutual induction over evaluator recursion. Each case either returns a control result directly, evaluates subterms covered by IHs, enters a scoped body covered by env-extension/scope-pop lemmas, or calls a lower soundness layer. Assignment branches are the strengthened call sites: target evaluation gives `target_runtime_typed`; expression/materialisation gives `value_has_type`; static typing gives `assignable_type`; bridge lemmas derive `assign_operation_runtime_typed`, `assign_operation_matches_target_shape`, and `assign_target_assignable_context`; C1 then proves assignment no-TypeError and runtime consistency for all results. Tuple/list assignment uses the second assignment theorem through `target_assignment_values_assignable`. Builtin/update and call expression cases delegate to C4/C5 rather than duplicating evaluator analysis.

#### Definition design
The important local interface is `assignment_value_static_assignable_context` and its bridge lemmas from runtime-typed target values plus `env_consistent` to full `assign_target_assignable_context`/`EVERY` context. Operation bridges should have conclusions that unify exactly with C1 premises for `Replace`, `Update`, append, and pop. Failure signs: statement cases inspect top-level storage/hashmap layout directly, tuple assignment manually recurses over targets, or AugAssign unfolds binop internals instead of using C4.

#### Code structure
Place statement-side bridges and resumes in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near `eval_all_type_sound_mutual`. Consume assignment theorem from `vyperTypeStatePreservation`; do not move C1 helpers here. Public wrappers remain in `vyperTypeSoundnessNewScript.sml` unless current source already exports compatibility lemmas from statement soundness.

### C2.1: Assignment assignable-context bridge lemmas
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: The current source reportedly already contains these predicates/lemmas; this is an audit or mechanical repair of direct projections.
- Dependencies: C1.6
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2.1

#### Progress note
Reuse existing `assignment_value_static_assignable_context` and bridge lemmas where they build.

#### Summary
- Ensure `assignment_value_static_assignable_context` and simplification lemmas build.
- Prove/reuse single-target context bridge from `target_runtime_typed` and `env_consistent`.
- Prove/reuse list bridge for `target_values_runtime_typed` and `EVERY assign_target_assignable_context`.
- Strengthen here if a statement branch lacks context facts.

#### Statement
```sml
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
Use the existing mutual runtime-typed induction/projection. Top-level cases draw storage/hashmap writability from env consistency and static declarations; scoped cases simplify directly.

#### Not to try
Do not derive assignable context from assignment success; assignment soundness needs it before execution, including for failing assignments.

### C2.2: Assignment operation runtime/shape bridge lemmas
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: Finite proofs from operation typing/value typing and C4 update-binop theorem; statements should be narrow and match C1 premises.
- Dependencies: C4.1
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2.2

#### Progress note
Existing Replace bridges can be carried forward; add exact append/pop/update bridges only for current call sites.

#### Summary
- Prove/reuse `Replace` runtime-typed and shape bridges from `value_has_type`.
- Add exact bridges for `Update`, append, and pop used by statement cases.
- Use `assignable_type_evaluate_not_NoneTV` for annotated assignment non-None facts.
- Conclusions must directly satisfy C1 premises.

#### Statement
```sml
Theorem assign_operation_runtime_typed_Replace_from_value_has_type: ...
Theorem assign_operation_matches_target_shape_Replace_from_typed: ...
(* plus exact Update/Append/Pop bridge lemmas required by current source *)
```

#### Approach
For `Replace`, split target value shape; tuple cases use tuple value typing and list lengths. For `Update`, use `well_typed_update_binop_no_type_error`/runtime typing from C4.1 and prove shape from the evaluated target shape.

#### Not to try
Do not hide missing update-binop proofs by cheating bridges. Do not use a large metis over full statement contexts when a two- or three-premise local lemma would be stable.

### C2.3: Prove assignment statement cases
- Kind: `proof_batch`
- Risk: 2
- Rationale: After C1 and C2.1-C2.2, AnnAssign/Assign/AugAssign are linear compositions of target/value IHs and assignment soundness.
- Dependencies: C2.1, C2.2
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2.3, PLAN_type_system_rewrite.md C2.4, PLAN_type_system_rewrite.md C2.5

#### Progress note
Merges the three assignment statement branches into one task-focused batch while preserving their distinct proof interfaces.

#### Summary
- Resume `AnnAssign`, `Assign`, and `AugAssign` cases.
- Derive assignable context from evaluated targets, not from assignment execution.
- Derive operation runtime typing and shape for `Replace`/tuple replace/update.
- Tuple/list assignment must call `cj 2 assign_target_sound_mutual` via `target_assignment_values_assignable`.

#### Statement
```sml
Resume eval_all_type_sound_mutual[AnnAssign]: ...
Resume eval_all_type_sound_mutual[Assign]: ...
Resume eval_all_type_sound_mutual[AugAssign]: ...
```

#### Approach
Follow evaluator order: evaluate target(s), evaluate value expression(s), materialise if necessary, form assignment operation premises, then apply C1. `AnnAssign` uses annotated `assignable_type`; `Assign` splits single vs tuple/list paths; `AugAssign` delegates update-binop safety to C4.1 through C2.2.

#### Not to try
Do not resurrect old `ty <> NoneT` side conditions; use `assignable_type`. Do not handle tuple assignment by repeated single-target proofs in the statement case. Do not unfold binop cases inside AugAssign.

### C2.4: Prove non-assignment and structured statement cases
- Kind: `proof_batch`
- Risk: 2
- Rationale: These cases are standard mutual-IH and scope/frame applications once assignment is settled.
- Dependencies: C2.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2.6, PLAN_type_system_rewrite.md C2.7

#### Progress note
Covers remaining statement/list/loop/iterator resumes not specifically assignment, builtin, or call.

#### Summary
- Resume literal control/result cases such as Pass, Break, Continue, Return, Raise, Assert, Log, and Expr.
- Resume sequence, if, loop, for-body, and iterator cases.
- Use env-extension, frame, and scope-pop lemmas for scoped execution.
- Use expression IHs only at their evaluator boundaries.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Pass]: ...
Resume eval_all_type_sound_mutual[Return_*]: ...
Resume eval_all_type_sound_mutual[If/For/Stmts/Iterator_*]: ...
```

#### Approach
For direct controls, simplify evaluator and typing definitions. For sequencing, destruct the first result and apply the next IH only in the success branch. For loops/scopes, use existing scope-bracket/pop preservation lemmas rather than raw scope-list reasoning.

#### Not to try
Do not inspect expression evaluator internals in these cases. Do not force block-success env consistency to be the extended body env when the theorem restores caller env after scope pop.

### C2.5: Prove target/base-target evaluation cases
- Kind: `proof_batch`
- Risk: 2
- Rationale: These cases are included in the mutual theorem to feed assignment soundness; they use path/place typing helpers and list IHs.
- Dependencies: C2.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2.8

#### Progress note
Keep target runtime typing separate from assignment context; context is derived later by C2.1.

#### Summary
- Resume target tuple/list/base-target cases.
- Successful targets produce `target_runtime_typed` or list runtime typing.
- Base targets produce shape/location/path facts required by later assignment branches.
- Subscript/attribute extend paths using existing type/path lemmas.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Target_Base/Target_Tuple/Targets_*]: ...
Resume eval_all_type_sound_mutual[BaseTarget_Name/BareGlobal/TopLevel/Subscript/Attribute]: ...
```

#### Approach
For base targets, apply subexpression/base-target IHs in evaluator order, then use static place-target, subscript, or attribute typing lemmas to extend `target_path_type`. For target lists, use structural list reasoning and the mutual IH to build `LIST_REL3`/list runtime typing.

#### Not to try
Do not prove top-level writability or layout-slot assignability here; this component proves runtime target typing only.

### C2.6: Prove expression/expression-list delegated cases inside statement mutual theorem
- Kind: `proof_batch`
- Risk: 2
- Rationale: Expression cases should be wrappers around the expression/builtin/call soundness layers; remaining work is projection and `expr_result_typed` reconstruction.
- Dependencies: C4, C5
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C2.9

#### Progress note
If current source keeps expression soundness in a separate theory, use its exported theorem rather than redoing evaluator recursion.

#### Summary
- Resume expression and expression-list cases still in `eval_all_type_sound_mutual`.
- Delegate builtin/type-builtin subcases to C4 theorems.
- Delegate call expression subcases to C5 wrappers.
- Preserve `expr_result_typed`, including place/hashmap reference invariants.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_*]: ...
Resume eval_all_type_sound_mutual[Exprs_*]: ...
```

#### Approach
Apply exported expression soundness where available; otherwise apply the expression IH in evaluator order and reconstruct `expr_result_typed_def`. Builtin and call cases should stop at their soundness theorem boundaries.

#### Not to try
Do not reintroduce retired helper statements from the old stack. Do not unfold builtin or call evaluators after their boundary theorem applies.

### C2.7: Statement soundness build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical build and warning audit after all statement mutual resumes are completed.
- Dependencies: C2.3, C2.4, C2.5, C2.6
- Checkpoint: yes

#### Progress note
Gates call/final soundness on a non-cheated statement/evaluator joint theorem.

#### Summary
- Build `vyperTypeStmtSoundnessTheory`.
- Confirm no unresolved `cheat` or `suspend` remains in `vyperTypeStmtSoundnessScript.sml`.
- Record remaining imported warnings from builtin/call layers separately.
- Escalate if theorem shape lacks a needed postcondition.

#### Statement
```sh
holbuild build vyperTypeStmtSoundnessTheory
```

#### Approach
Use build output and targeted grep. If multiple cases need the same missing invariant, strengthen the mutual theorem and callers rather than proving duplicate case-local facts.

#### Not to try
Do not claim statement soundness complete if it builds only by importing cheated builtin/call facts; final zero-CHEAT is C6’s criterion.

### C3: Audit/prove assignment compatibility wrappers
- Kind: `compatibility_wrappers`
- Risk: 1
- Rationale: The wrappers named by the TASK should be corollaries of C1. If current source already proves them, this is a mechanical audit; otherwise projection from C1 is standard.
- Required for completion: yes
- Dependencies: C1.6
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C3

#### Progress note
These wrappers are public/compatibility surface only. Internal proofs should use `assign_target_sound_mutual`.

#### Summary
- Verify or reprove `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error` in `vyperTypeAssignSoundnessScript.sml`.
- Prove wrappers as projections of the joint assignment theorem where needed.
- Keep wrapper statements compatible with current callers.
- Build/audit `vyperTypeAssignSoundnessTheory` with no fresh-file cheats.

#### Statement
```sml
Theorem assign_target_no_type_error: ...
Theorem assign_target_update_no_type_error: ...
Theorem assign_target_append_no_type_error: ...
```

#### Approach
First audit current proofs. If any wrapper is cheated or broken, instantiate `cj 1 assign_target_sound_mutual` with the wrapper’s operation-specific premises and simplify `no_type_error_result`.

#### Not to try
Do not restore standalone recursive assignment-wrapper proofs. Do not weaken wrapper behavior; the stronger internal theorem is already available.

#### Argument
The compatibility wrappers expose legacy no-TypeError names but should not drive the architecture. Since C1 proves all-result runtime consistency and `no_type_error_result` for any well-typed/assignable assignment operation, each wrapper follows by supplying operation-specific runtime/shape/context premises and projecting the no-TypeError conclusion.

#### Definition design
No new definitions. If a wrapper lacks a premise needed by C1, use an existing operation/context bridge or prove a narrow wrapper-side bridge; do not alter C1.

#### Code structure
All wrapper work stays in `semantics/prop/vyperTypeAssignSoundnessScript.sml`. Keep any helper local unless imported by statement/call soundness.

### C4: Finish builtin/binop/type-builtin no-TypeError layer
- Kind: `proof_subtree`
- Risk: 3
- Rationale: Derived from child component C4.1 risk 3. ">~ is an infix operator that pairs a tactic with a quotation list, not a standalone filtering step. Cannot use >~ after >>. Need different goal routing architecture. Also need to handle Not case for bool/uint (not just flag), and Keccak256/Sha256 need evaluate_type_def expansion with Cases_on bd for abstract bd variable."
- Required for completion: yes
- Dependencies: C0
- Supersedes: prior slice-only builtin PLAN C1, PLAN_type_system_rewrite.md C4 risk-3 formulation
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4, E0158, E0159, E0160

#### Progress note
Refines the earlier C4 risk-3 note by making ECRecover list extraction a checkpoint helper and keeping all children risk 1-2. Supersedes old slice-only builtin work by treating it as one branch under the builtin layer.

#### Summary
- Prove `well_typed_binop_no_type_error`, update-binop facts, and assignment-subscript update path lemmas.
- Prove remaining builtin/type-builtin no-TypeError dispatcher cases, including ECRecover, ABI encode/decode, Env/MsgGas, and simple projections.
- Keep all fixes localized to `vyperTypeBuiltinsScript.sml` unless a checked probe proves executable typing/runtime mismatch.
- Export only dispatcher/update lemmas consumed downstream.

#### Statement
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
Use per-constructor boundary lemmas, then prove dispatcher theorems by case analysis over typing/evaluator constructors. For update assignment, prove binop/update-binop no-TypeError once and reuse it in recursive subscript lemmas.

#### Not to try
Do not unfold ABI/crypto/bytes arithmetic in the global dispatcher; isolate it behind branch lemmas. Do not patch assignment or AugAssign with local cheats if update-binop facts are missing. Do not silently change Env/MsgGas behavior without a probe.

#### Argument
Builtin soundness is finite case analysis. Static typing fixes arity, result type, and evaluated argument type values; `LIST_REL value_has_type` fixes runtime value constructors. Each branch must show that evaluator failures are either normal results or non-TypeError runtime errors. Binop soundness is the shared boundary for update assignment: typed update binops cannot raise TypeError and preserve the expected type, so recursive assignment-subscript update lemmas inherit both no-TypeError and preservation. ABI/crypto/env/type-builtin details remain hidden behind branch lemmas consumed by expression/statement soundness.

#### Definition design
No broad new framework. Add small local boundary lemmas named after evaluator operations. Use probes only for suspected typing/runtime mismatches such as Env/MsgGas or ABI bounds. A branch lemma is too weak if the dispatcher proof still needs to destruct ABI encodings or cryptographic internals.

#### Code structure
All work belongs in `semantics/prop/vyperTypeBuiltinsScript.sml`. Keep per-branch helpers `[local]` except update/subscript lemmas imported by state preservation. Edit lower typing/evaluator files only after a checked probe establishes mismatch and the TASK permits internal repair.

### C4.1: Close the binop/update-binop no-TypeError path and its builtin dispatcher prerequisite
- Kind: `proof_batch`
- Risk: 2
- Rationale: The false AsWeiValue typing issue was already repaired in source (AsWeiValue now uses uint-only typing per prior evidence), and the remaining blocker is proof-organization/syntax in `well_typed_builtin_app_no_type_error`, not a mathematical unknown. The assignment-subscript lemmas in `vyperTypeStatePreservationScript.sml` now have direct statements and proof skeletons that reduce to the already-proved `well_typed_binop_no_type_error`; this makes the remaining work a standard dispatcher rebuild plus build/audit.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0168, E0169, E0170, E0171, E0172, E0173, E0174, E0175, E0176, E0177

#### Progress note
This refines the stuck C4.1 rather than replacing its obligation. Prior episodes established the binop proof direction, repaired the AsWeiValue typing definition, proved EC point boundary helpers, and identified the exact final blocker: invalid `>~` routing and mixed builtin categories in `well_typed_builtin_app_no_type_error`. Those results still support the revised component; the executable plan is narrowed to a syntactically valid per-category dispatcher and an audit of the update-binop assignment-subscript chain. Because this is an augment inside dotted component C4.1, `required_for_completion` is false here and inherited from the existing top-level component in the broader plan.

#### Summary
- Prove/build the C4.1 no-TypeError chain that supports update assignment through `assign_subscripts`.
- First repair the strict prerequisite `well_typed_builtin_app_no_type_error` proof in `vyperTypeBuiltinsScript.sml`; do not use `>~` as a standalone tactic.
- Then audit/build the state-preservation update-binop lemmas: `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`.
- The core mathematical invariant is that the static binop/update typing judgment gives evaluator arguments with constructors expected by `evaluate_binop`, so no `TypeError` branch can be reached.
- Finish with a checkpoint build sufficient to show this subtree no longer blocks downstream assignment-target work.

#### Description
C4.1 owns the inherited binop/update-binop no-TypeError path and the strict builtin-file proof prerequisite needed before `vyperTypeStatePreservationTheory` can build. Stay within `vyperTypeBuiltinsScript.sml` and `vyperTypeStatePreservationScript.sml` at the named theorems/helpers only. Do not attempt the later builtin success-type cheats, ABI encode branches, raw-call bound cheat, or assignment-target mutual suspended branches; those are siblings/cousins outside this subtree unless they become build blockers for these exact theorems.

#### Approach
First make the builtin dispatcher syntactically valid and category-directed, because the state-preservation file imports `vyperTypeBuiltins`. Then build/audit the update-binop assignment-subscript chain. Use theorem statements already in source as authoritative and only strengthen local helpers if the exact named statement cannot be proved directly.

#### Not to try
Do not resurrect the invalid `>> >~ [...]` style: `>~` is an infix routing combinator and cannot be used as a standalone tactic after `>>`. Do not use one large `gvs[evaluate_builtin_def]` catch-all before delegation; it destroys the shape of Concat/Slice goals and leaves crypto hash goals blocked on abstract bounds. Do not start proving later builtin success typing or ABI encode cheats under this component.

#### Argument
The path has two layers. At the builtin/binop layer, `well_typed_builtin_app_no_type_error` is a dispatcher over builtin constructors. Most builtin constructors are already covered by local boundary lemmas (`well_typed_binop_no_type_error`, `flag_Not_no_type_error`, `as_wei_value_uint_no_type_error`, `make_array_no_type_error`, `ecadd_no_type_error`, `ecmul_no_type_error`, `ecrecover_no_type_error`, `concat_no_type_error`, `slice_no_type_error`, and string variants). The proof must preserve the conclusion shape expected by those helpers: apply `irule` before expanding `evaluate_builtin_def` for Concat/Slice/EC helpers, and expand/evaluate only after the helper is no longer needed. Crypto hash cases require destructing the abstract bytes bound (`Cases_on bd`) before simplifying `evaluate_type_def`, because otherwise simplification leaves a blocked case expression.

At the assignment-subscript layer, update assignment reduces at the leaf to `evaluate_binop`; the static predicate `assign_operation_runtime_typed env leaf_ty op` gives an evaluated leaf type and RHS runtime type matching the update binop judgment. The leaf no-TypeError theorem proves each operation constructor separately; the non-leaf theorem is structural induction over `subs`, preserving a value typing fact down through array indices and struct fields until the leaf theorem applies. Preservation is analogous but uses `assign_subscripts_preserves_type` plus the existing operation leaf-type lemmas, rather than redoing subscript recursion.

#### Definition design
No new semantic definitions should be introduced. The proof interface should stay theorem-based:

- `evaluate_type_BaseT_SOME` and `evaluate_type_ArrayT_SOME` are inversion boundaries from source types to runtime type values. Use these to avoid unfolding all of `evaluate_type_def` in large goals.
- Constructor-shape lemmas such as `vht_BaseTV_*` and `vht_ArrayTV_exists` are the value-inversion boundary. Use them to convert `value_has_type` into the exact value constructor expected by the evaluator.
- Builtin helper lemmas should consume the unexpanded `evaluate_builtin ... blt ...` conclusion where possible. This is especially important for Concat/Slice: expanding `evaluate_builtin_def` changes the head symbol to `evaluate_concat`/`evaluate_slice` and breaks `irule` matching.
- Failure signs: a proof that creates dozens of unrelated builtin subgoals after `Cases_on blt`, a goal containing a stuck `case bd of ...` after simplification, or a Concat/Slice goal whose conclusion no longer mentions `evaluate_builtin` indicates that expansion happened too early.

#### Code structure
Make only localized edits.

- In `semantics/prop/vyperTypeBuiltinsScript.sml`, repair/prove helper lemmas immediately above `well_typed_builtin_app_no_type_error` if needed, then replace only that theorem's proof body. Prefer local helper theorems for category dispatch if the monolithic proof remains brittle.
- In `semantics/prop/vyperTypeStatePreservationScript.sml`, only touch the named update-binop/subscript lemmas if the build shows they are not accepted. The current source already contains direct proofs for these statements; preserve their theorem names because downstream assignment proofs call them.
- Do not edit `vyperTypeSoundnessScript.sml` old retired proofs, later builtin success-type theorems, ABI encode resumed branches, or the assignment-target mutual theorem in this component.

### C4.1.1: Repair the no-TypeError builtin dispatcher without standalone `>~` routing
- Kind: `proof`
- Risk: 2
- Rationale: Prior episodes identified all remaining builtin categories and the exact syntactic blocker. A constructor case split on `blt` plus valid per-case `>-` branches or local category helper theorems is a standard HOL4 proof organization issue.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0174, E0175, E0176, E0177

#### Progress note
Carries forward the diagnosis that the theorem itself is plausible after the AsWeiValue source repair, but the previous proof architecture was invalid due to standalone `>~` and over-eager expansion.

#### Summary
- Replace the proof body of `well_typed_builtin_app_no_type_error` in `vyperTypeBuiltinsScript.sml`.
- Keep the theorem statement unchanged.
- Route builtin constructors using valid HOL4 structure: either explicit `Cases_on blt` branches with `>-`, or local per-constructor/per-category helper theorems consumed by `irule`.
- Handle Bop, Not, AsWeiValue, EC, MakeArray, Env, Acc, crypto hashes, Concat/Slice, and remaining simple builtins separately.
- Checkpoint when `vyperTypeBuiltinsTheory` gets past this theorem.

#### Statement
Theorem well_typed_builtin_app_no_type_error:
  well_typed_builtin_app ty blt ts ∧ blt ≠ Len ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧ accounts_well_typed acc ∧
  (!item. blt = Env item ==> item ≠ MsgGas) ==>
  !msg. evaluate_builtin cx acc ty blt vs <> INR (TypeError msg)

#### Approach
After `strip_tac >> Cases_on blt`, simplify only `well_typed_builtin_app_def`, length facts, and classifier inversion lemmas. For cases with existing helper lemmas, apply `irule` before expanding `evaluate_builtin_def`; solve premises with the existing MAP/LIST_REL/evaluate_type assumptions. For remaining direct cases, use `evaluate_type_BaseT_SOME`, value constructor inversions, and only then simplify `evaluate_builtin_def`.

#### Not to try
Do not write `>> >~ [...]`; it is syntactically invalid in this position. Do not make helper theorems with antecedents like `blt = Concat ∨ blt = Slice` and then `Cases_on blt` inside them; that creates every builtin constructor subgoal and repeats the original problem. Do not expand `evaluate_builtin_def` before trying `concat_no_type_error` or `slice_no_type_error`.

### C4.1.1.1: Optionally introduce exact local crypto-hash no-TypeError helpers
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: The crypto hash cases are direct definition/value-shape proofs once the argument type is known to be bytes or string. They are isolated and prevent the dispatcher from depending on fragile goal routing.
- Carries progress/evidence from: E0175, E0176

#### Progress note
This child is optional but owned by C4.1.1; use it if the main dispatcher remains cumbersome. Prior evidence identified `Cases_on bd` before `evaluate_type_def` as the key step.

#### Summary
- If useful, prove local helper(s) for `Keccak256` and `Sha256` before the main dispatcher.
- The helpers should have concrete builtin constructors in the conclusion/assumptions, not a variable `blt` plus disjunction.
- Split the well-typed argument type into `BytesT bd` vs `StringT m`; for `BytesT`, `Cases_on bd` before simplifying `evaluate_type_def`.
- Conclude by expanding `evaluate_builtin_def` after value constructors are known.

#### Statement
Suggested local shape, either duplicated or parameterized by the two concrete constructors:

Theorem keccak256_no_type_error[local]:
  well_typed_builtin_app ty Keccak256 ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==> 
  !msg. evaluate_builtin cx acc ty Keccak256 vs <> INR (TypeError msg)

Theorem sha256_no_type_error[local]:
  same shape with `Sha256`.

#### Approach
Simplify `well_typed_builtin_app_def` to get the single argument and its bytes/string typing. For bytes, destruct the bound variable with `Cases_on bd` before `gvs[evaluate_type_def]`; for string, `gvs[evaluate_type_def]` is enough. Then destruct `vs` and the argument value and finish with `simp[evaluate_builtin_def]`.

#### Not to try
Do not leave the constructor abstract as `blt` in these helpers. Do not simplify `evaluate_type_def` on `BytesT bd` before splitting `bd`, or the goal may contain a stuck case expression.

### C4.1.1.2: Optionally introduce exact local Concat/Slice no-TypeError dispatcher helpers
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: Existing `concat_no_type_error`, `concat_string_no_type_error`, `slice_no_type_error`, and `slice_string_no_type_error` already contain the evaluator reasoning. Exact dispatcher helpers merely preserve conclusion shape and package length/type premises.
- Carries progress/evidence from: E0176, E0177

#### Progress note
This child is optional and refines the prior failed disjunction-helper idea into exact constructor helpers that do not case split over all builtins.

#### Summary
- If direct dispatcher branches are brittle, add local exact helpers for `Concat` and `Slice`.
- Each helper should name one concrete builtin constructor and internally choose bytes vs string branch from `well_typed_builtin_app_def`.
- Apply the existing Concat/Slice evaluator lemmas before unfolding `evaluate_builtin_def`.
- Use LIST_REL/MAP length facts and `evaluate_type_def` only for side conditions such as size bounds.

#### Statement
Suggested local shapes:

Theorem concat_builtin_no_type_error[local]:
  well_typed_builtin_app ty Concat ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty Concat vs <> INR (TypeError msg)

Theorem slice_builtin_no_type_error[local]:
  same shape with `Slice`.

#### Approach
Open `well_typed_builtin_app_def` just enough to obtain the bytes/string disjunction and argument length. In each branch, immediately `irule concat_no_type_error`/`concat_string_no_type_error` or `slice_no_type_error`/`slice_string_no_type_error`, then discharge premises using `LIST_REL_LENGTH`, `LENGTH_MAP`, and type evaluation facts. Only unfold `evaluate_type_def` for arithmetic/size premises after the helper is applied.

#### Not to try
Do not unfold `evaluate_builtin_def` first. Do not create a combined `Concat ∨ Slice` helper that internally performs `Cases_on blt`; it recreates all constructor subgoals.

### C4.1.1.3: Handle Not and simple builtin cases explicitly in the dispatcher
- Kind: `proof_slice`
- Risk: 2
- Rationale: Prior evidence notes that `Not` has bool and flag/int-like cases, not just flag. The simple builtins are direct constructor/value-shape computations once the type evaluator and value typing assumptions are inverted.
- Progress transition: `refinement`
- Carries progress/evidence from: E0174, E0177

#### Progress note
Refines the old catch-all direct-simplification phase by making explicit that `Not` may need more than `flag_Not_no_type_error`, and simple cases should be handled after type/value inversion.

#### Summary
- In `well_typed_builtin_app_no_type_error`, do not rely solely on `flag_Not_no_type_error` for the `Not` constructor.
- Add an explicit bool `Not` branch by deriving `BoolV` from `is_bool_type`/`evaluate_type`/`value_has_type` and simplifying `evaluate_builtin_def`.
- For simple numeric/hash/method builtins, derive `BaseTV` via `evaluate_type_BaseT_SOME`, destruct the relevant runtime values, then simplify evaluator definitions.
- Keep this work in the main theorem proof unless a local helper makes the proof clearer.

#### Statement
No separate public theorem required. This is the `Not`, `Neg`, `Ceil`, `Floor`, `AddMod`, `MulMod`, `PowMod256`, `BlockHash`, `BlobHash`, `MethodId`, `Uint2Str`, and similar direct-computation cases inside `well_typed_builtin_app_no_type_error`.

#### Approach
For `Not`, split the static type alternatives exposed by classifier inversion; use `flag_Not_no_type_error` only in the flag branch and direct `BoolV` inversion in the bool branch. For simple cases, repeatedly apply type inversion (`evaluate_type_BaseT_SOME`) and value inversion (`Cases_on v` plus `value_has_type_def` or local `vht_*` lemmas) before expanding the evaluator. Use `intLib.ARITH_TAC` only for residual arithmetic side conditions.

#### Not to try
Do not hide these cases under a `TRY` catch-all that silently backtracks; failures then fall into inappropriate expansions. Do not assume `Not` is flag-only.

### C4.1.2: Audit and build the update-binop assignment-subscript no-TypeError chain
- Kind: `proof_audit`
- Risk: 1
- Rationale: The current source already contains direct proofs for the named state-preservation theorems, and their dependency on `well_typed_binop_no_type_error` is explicit. Once the builtin theory builds, this is a mechanical build/audit rather than theorem design.
- Dependencies: C4.1.1
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0168, E0169, E0170, E0171

#### Progress note
Carries forward prior binop proof progress and the current source evidence showing these lemmas are no longer cheated. The component exists to confirm the chain under `holbuild` and make only localized fixes if the accepted source differs from the displayed context.

#### Summary
- Build/audit the five update-binop/subscript theorems in `vyperTypeStatePreservationScript.sml`.
- Preserve their names and statements because downstream assignment preservation calls them.
- Expected proof chain: update leaf delegates to `well_typed_update_binop_no_type_error`; operation leaf cases split on `op`; recursive subscript no-TypeError inducts on `subs`; preservation delegates to `assign_subscripts_preserves_type`.
- If any proof fails, fix only the local proof, not the statement, unless HOL shows the current statement is false.

#### Statement
Named obligations in `vyperTypeStatePreservationScript.sml`:

- `assign_subscripts_preserves_type_runtime_typed`
- `well_typed_update_binop_no_type_error`
- `assign_subscripts_update_leaf_no_type_error`
- `assign_operation_runtime_typed_leaf_no_type_error`
- `assign_subscripts_no_type_error_runtime_typed`

#### Approach
Run the build after C4.1.1. If these theorems are already accepted, record the checkpoint and do not edit them. If a local failure appears, follow the current proof architecture: `well_typed_update_binop_no_type_error` is the assignment-shaped instance of `well_typed_binop_no_type_error`; leaf update unfolds `assign_subscripts_def`; recursive no-TypeError uses induction over `subs` and value typing preservation for array/struct descent.

#### Not to try
Do not start a second evaluator induction or duplicate the binop case analysis here. Do not weaken `assign_operation_runtime_typed`; downstream assignment soundness depends on the stronger runtime-typed operation invariant. Do not touch assignment-target mutual suspended branches in this component.

### C4.1.3: Checkpoint build for the C4.1 subtree
- Kind: `build_checkpoint`
- Risk: 1
- Rationale: This is a mechanical validation step after the dispatcher and update-subscript chain have been handled. It determines whether C4.1 can be marked unblocked without planning unrelated cheats.
- Dependencies: C4.1.1, C4.1.2
- Checkpoint: yes

#### Progress note
New validation child added to ensure the refined subtree has objective build evidence before control returns to sibling components.

#### Summary
- Run `holbuild build vyperTypeBuiltinsTheory` first to validate the repaired dispatcher.
- Then run `holbuild build vyperTypeStatePreservationTheory` or the nearest target that reaches the update-binop/subscript lemmas.
- Success means C4.1's scoped obligations are discharged, even if later unrelated cheats in the same files still warn.
- If the build stops at a later theorem outside C4.1 (e.g. builtin success-type ABI encode or assignment-target mutual branches), report that as outside-subtree blockage rather than editing it here.

#### Statement
Build evidence obligations:

```sh
holbuild build vyperTypeBuiltinsTheory
holbuild build vyperTypeStatePreservationTheory
```

#### Approach
Use the first build to catch syntax/proof issues in `well_typed_builtin_app_no_type_error`. Use the second to verify that imports and the named update-subscript lemmas are accepted in their actual dependency context. Treat CHEAT warnings from later unrelated theorems as notes, not C4.1 failures, unless they are one of the named C4.1 obligations.

#### Not to try
Do not chase every CHEAT warning from these builds under C4.1. Do not edit old `vyperTypeSoundnessScript.sml` even if grep reports cheats there; it is outside this component and retired unless the broader task plan says otherwise.

### C4.2: Prove ECRecover no-TypeError via runtime boundary and robust list extraction
- Kind: `proof_subtree`
- Risk: 2
- Rationale: Prior evidence proved semantic converter boundaries; the hard part is isolated to standard fixed-length list extraction with EL-index reasoning.
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4.2, E0158, E0159, E0160
- Invalidates prior progress/evidence: fragile inline ECRecover list destruct proof attempt

#### Progress note
Replaces the brittle proof pattern that depended on `gvs`-generated tail names. The theorem statement remains current-source exact.

#### Summary
- Keep `ecrecover_no_type_error` statement unchanged.
- Reuse converter and `evaluate_ecrecover` boundary lemmas.
- Add a runtime four-argument ECRecover safety lemma.
- Add a static/list extraction lemma using EL-index or disciplined fixed-length destruct.
- Compose those helpers for the final local theorem.

#### Description
This subtree is limited to ECRecover in `vyperTypeBuiltinsScript.sml`. It must not re-plan unrelated builtin branches.

#### Statement
```sml
Theorem ecrecover_no_type_error[local]:
  LENGTH ts = 4 /\ ty = BaseT AddressT /\
  HD ts = BaseT (BytesT (Fixed 32)) /\
  EVERY (\t. t = BaseT (UintT 256) \/ t = BaseT (BytesT (Fixed 32))) (TL ts) /\
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty ECRecover vs <> INR (TypeError msg)
```

#### Approach
First prove runtime ECRecover safety for `[v0;v1;v2;v3]`. Then prove the list extraction lemma from `LENGTH`, `HD`, `EVERY (TL ...)`, `MAP evaluate_type`, and `LIST_REL`. The final theorem only extracts witnesses, rewrites `ty`, and applies runtime safety.

#### Not to try
Do not repeat `Cases_on vs >> gvs[LIST_REL_CONS1]` with references to generated tail names. Do not unfold `evaluate_builtin_def` before extracting the four runtime values.

#### Argument
ECRecover can produce TypeError only if the wrapper sees the wrong argument shape or `evaluate_ecrecover` rejects the four runtime arguments. The typing hypotheses force a four-element value list: first value has fixed bytes32 type, and each of the last three values has either uint256 or bytes32 type, both accepted by `ecrecover_arg_to_num`. Therefore `evaluate_ecrecover` is called with a bytes32 hash and three convertible arguments, ruling out TypeError.

#### Definition design
Use local helper theorems only: converter-not-none facts, `evaluate_ecrecover_no_type_error`, `ecrecover_runtime_args_no_type_error`, and `ecrecover_args_typed_from_lists`. No semantic definition change.

#### Code structure
Place helpers immediately above existing `ecrecover_no_type_error[local]` in `vyperTypeBuiltinsScript.sml`; keep them `[local]`.

### C4.2.1: Carry forward ECRecover converter/evaluator boundaries
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: These are direct value case splits and were already reported proved in prior episodes.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0158, E0159

#### Progress note
Only adjust if current source names/statements drift.

#### Summary
- Reuse/prove converter lemmas for uint256 and bytes32 arguments.
- Reuse/prove `evaluate_ecrecover_no_type_error`.
- Keep these independent of static argument lists.
- They feed the runtime four-argument lemma.

#### Statement
```sml
Theorem ecrecover_arg_Uint256_not_none[local]: ...
Theorem ecrecover_arg_BytesT32_not_none[local]: ...
Theorem evaluate_ecrecover_no_type_error[local]: ...
```

#### Approach
Case split on values for converter lemmas. For `evaluate_ecrecover`, rewrite its definition and use non-`NONE` converter hypotheses to eliminate bad branches.

#### Not to try
Do not mention `ts`, `tvs`, or `well_typed_builtin_app` in these semantic boundaries.

### C4.2.2: Runtime ECRecover arguments rule out builtin TypeError
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: Small wrapper over C4.2.1 plus one first-argument shape split.
- Dependencies: C4.2.1
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4.2.2

#### Progress note
Packages ECRecover internals so the final theorem does no evaluator reasoning.

#### Summary
- Prove local lemma for concrete list `[v0;v1;v2;v3]`.
- First arg has bytes32 type.
- Last three args have uint256-or-bytes32 type.
- Conclusion is directly `evaluate_builtin ... ECRecover ... <> INR (TypeError msg)`.

#### Statement
```sml
Theorem ecrecover_runtime_args_no_type_error[local]:
  !cx acc v0 v1 v2 v3 msg.
    value_has_type (BaseTV (BytesT (Fixed 32))) v0 /\
    (value_has_type (BaseTV (UintT 256)) v1 \/ value_has_type (BaseTV (BytesT (Fixed 32))) v1) /\
    (value_has_type (BaseTV (UintT 256)) v2 \/ value_has_type (BaseTV (BytesT (Fixed 32))) v2) /\
    (value_has_type (BaseTV (UintT 256)) v3 \/ value_has_type (BaseTV (BytesT (Fixed 32))) v3) ==>
    evaluate_builtin cx acc (BaseT AddressT) ECRecover [v0; v1; v2; v3] <> INR (TypeError msg)
```

#### Approach
Use converter lemmas to prove the last three converter calls are not `NONE`. Split the first value or use a bytes-fixed value typing lemma to obtain `BytesV hash_bytes` with length 32, then rewrite the ECRecover branch and apply `evaluate_ecrecover_no_type_error`.

#### Not to try
Do not destruct static type lists here. Avoid simplification that consumes the `value_has_type` hypotheses before converter lemmas are applied.

### C4.2.3: Extract ECRecover runtime argument typing from list hypotheses
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: The previously fragile step is now isolated; EL-index reasoning over fixed length lists is standard and name-stable.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0160
- Invalidates prior progress/evidence: inline ECRecover `gvs[LIST_REL_CONS1]` tail-name proof

#### Progress note
This checkpoint confirms the replacement for the known stuck proof-engineering issue.

#### Summary
- Prove `vs` is a four-element list from `MAP` and `LIST_REL` lengths.
- Extract values `v0..v3` and their runtime typing predicates.
- Use `HD ts` for index 0 and `EVERY_EL` over `TL ts` for indices 1-3.
- Avoid generated tail names entirely.

#### Statement
```sml
Theorem ecrecover_args_typed_from_lists[local]:
  !cx ts tvs vs.
    LENGTH ts = 4 /\
    HD ts = BaseT (BytesT (Fixed 32)) /\
    EVERY (\t. t = BaseT (UintT 256) \/ t = BaseT (BytesT (Fixed 32))) (TL ts) /\
    MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
    LIST_REL value_has_type tvs vs ==>
    ?v0 v1 v2 v3.
      vs = [v0; v1; v2; v3] /\
      value_has_type (BaseTV (BytesT (Fixed 32))) v0 /\
      (value_has_type (BaseTV (UintT 256)) v1 \/ value_has_type (BaseTV (BytesT (Fixed 32))) v1) /\
      (value_has_type (BaseTV (UintT 256)) v2 \/ value_has_type (BaseTV (BytesT (Fixed 32))) v2) /\
      (value_has_type (BaseTV (UintT 256)) v3 \/ value_has_type (BaseTV (BytesT (Fixed 32))) v3)
```

#### Approach
Preferred: derive `LENGTH tvs = 4` and `LENGTH vs = 4`, instantiate witnesses with `EL 0..3 vs`, and use `LIST_REL_EL_EQN`, `EL_MAP`, and `EVERY_EL`. Fallback: fixed-length destruct `ts/tvs/vs` with immediate renaming and conservative `fs/simp`, not broad `gvs`.

#### Not to try
Do not prove raw constructors for the last three args; the disjunctive `value_has_type` predicate is the intended abstraction. Do not unfold `evaluate_builtin_def` here.

### C4.2.4: Prove exact `ecrecover_no_type_error`
- Kind: `proof`
- Risk: 1
- Rationale: Immediate composition after runtime and list-extraction helpers.
- Dependencies: C4.2.2, C4.2.3
- Progress transition: `refinement`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4.2.4

#### Progress note
Only replaces the proof body; statement remains current-source exact.

#### Summary
- Use list extraction to get `vs = [v0;v1;v2;v3]` and runtime typing.
- Rewrite `ty = BaseT AddressT`.
- Apply `ecrecover_runtime_args_no_type_error`.
- Avoid any further list destruct.

#### Statement
```sml
Theorem ecrecover_no_type_error[local]: ...
```

#### Approach
Strip the theorem assumptions, call `ecrecover_args_typed_from_lists`, destruct witnesses, simplify `ty` and `vs`, then apply the runtime ECRecover lemma.

#### Not to try
Do not start with `gvs[evaluate_builtin_def]`; it reintroduces the fragile proof shape.

### C4.3: Prove ABI encode/decode builtin branches
- Kind: `proof_batch`
- Risk: 2
- Rationale: The TASK identifies ABI bound issues as localized; branch boundary lemmas under typing-derived size facts should suffice, with probe-before-repair if not.
- Dependencies: C4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4.3

#### Progress note
Any previously proved slice/ABI helper may be reused here.

#### Summary
- Close ABI decode, ABI encode, tuple encode, and nowrap encode builtin dispatcher cases.
- Prove local no-TypeError boundaries under exact typing-derived bounds.
- If a bound is missing, create a small probe before changing internal typing/runtime.
- Keep ABI arithmetic out of statement/expression proofs.

#### Statement
```sml
Resume well_typed_builtin_app_no_type_error[abi_decode]: ...
Resume well_typed_builtin_app_no_type_error[abi_encode]: ...
Resume well_typed_builtin_app_no_type_error[encode_tuple]: ...
Resume well_typed_builtin_app_no_type_error[encode_tuple_nowrap]: ...
```

#### Approach
Normalize arity/type-list assumptions from executable typing, then apply or add ABI boundary lemmas whose hypotheses are exactly those normalized facts plus `value_has_type`. Use `vyperTypeABI` helper theorems where available.

#### Not to try
Do not add arbitrary numeric assumptions to dispatcher theorems unless they are derivable from executable typing or justified by a checked repair.

### C4.4: Prove Env/Acc and remaining ordinary builtin branches
- Kind: `proof_batch`
- Risk: 2
- Rationale: Most remaining branches are finite projections from context/account well-typedness or constructor simplification; MsgGas is handled by the required probe-before-repair discipline.
- Dependencies: C4.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4.4

#### Progress note
Scope is all current remaining ordinary builtin dispatcher suspends/cheats after C4.1-C4.3.

#### Summary
- Close Env, Acc, block/blob hash, method id, crypto, arithmetic utility, make-array, ceil/floor, slice, and other simple builtin cases present in current source.
- For `Env MsgGas`, inspect/probe executable typing/evaluator agreement before proof or repair.
- Use context/account invariants for projections.
- Keep each nontrivial constructor behind a local boundary lemma.

#### Statement
```sml
Resume well_typed_builtin_app_no_type_error[Env]: ...
Resume well_typed_builtin_app_no_type_error[Acc]: ...
(* plus remaining current ordinary builtin constructor cases *)
```

#### Approach
For projection builtins, unfold the branch and use `context_well_typed`/`accounts_well_typed` fields to show returned values have the expected constructor and no TypeError branch fires. For MsgGas, first check a concrete typing/evaluation branch; repair only if the executable definitions disagree.

#### Not to try
Do not make MsgGas unreachable by assumption unless executable typing rejects it. Do not change public semantics; only internal alignment repairs are allowed after probe evidence.

### C4.5: Prove type-builtin no-TypeError dispatcher
- Kind: `proof_batch`
- Risk: 2
- Rationale: Type-builtin cases are finite and self-contained once conversion/default/ABI helper facts are available.
- Dependencies: C4.3, C4.4
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C4.5

#### Progress note
Keep ordinary builtin and type-builtin dispatchers separate if current source does so.

#### Summary
- Prove remaining cases in `well_typed_type_builtin_app_no_type_error` or current equivalent.
- Use conversion/default/ABI helper theories.
- Ensure successful values fit expression-result typing consumers.
- Add local branch helpers for nontrivial conversions.

#### Statement
```sml
Theorem well_typed_type_builtin_app_no_type_error: ...
```

#### Approach
Case split on type-builtin constructor and evaluated type value. Defaults/constructors simplify directly; conversions use existing conversion no-TypeError/value typing lemmas.

#### Not to try
Do not merge type-builtin proofs into the ordinary dispatcher if source keeps them separate. Do not unfold conversion internals in statement soundness.

### C4.6: Builtin theory build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical build/warning audit after all builtin branch proofs.
- Dependencies: C4.1, C4.2.4, C4.3, C4.4, C4.5
- Checkpoint: yes

#### Progress note
Confirms the imported builtin layer no longer contributes CHEAT warnings to assignment/statement/final builds.

#### Summary
- Build `vyperTypeBuiltinsTheory`.
- Confirm no cheat/suspend remains in `vyperTypeBuiltinsScript.sml`.
- Confirm update-binop/subscript exported lemmas are trusted.
- Escalate with probe output if any typing/runtime mismatch remains.

#### Statement
```sh
holbuild build vyperTypeBuiltinsTheory
```

#### Approach
Use build log and targeted grep. Remaining failures should be localized to named constructors before downstream theories are rebuilt.

#### Not to try
Do not proceed to final `vyperSemanticsHolTheory` zero-CHEAT audit with builtin warnings still present.

### C5: Prove call soundness wrappers in `vyperTypeCallSoundnessScript.sml`
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The task names four call wrappers; they should be projections of statement/body soundness and finite external/special call boundaries, not a new evaluator induction.
- Required for completion: yes
- Dependencies: C2, C4
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C5

#### Progress note
Current SML wrapper statements are authoritative unless they conflict with frozen public behavior; if a wrapper is too strong, escalate with evidence before changing it.

#### Summary
- Prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error`.
- Use a joint internal-call body lemma if wrappers share setup proof.
- External/special calls use builtin/ABI/context/account boundaries from C4.
- Complete with a call theory zero-cheat audit.

#### Statement
```sml
Theorem internal_call_no_type_error: ...
Theorem internal_call_type_preservation: ...
Theorem external_call_no_type_error: ...
Theorem special_call_no_type_error: ...
```

#### Approach
For internal calls, unfold setup only until a typed callable body/list of statements is evaluated, apply C2, and project. For external/special calls, unfold the finite call branch and dispatch ABI/builtin runtime checks via C4.

#### Not to try
Do not duplicate statement evaluator induction in call soundness. Do not prove internal no-TypeError and preservation by two separate setup proofs if a joint lemma can project both.

#### Argument
Calls enter the same typed runtime world as statements. Argument/default binding and local scope setup preserve env/state/account invariants; the body is typed under the extended environment; C2 covers body evaluation and return/exception typing; scope/frame lemmas restore caller invariants. External/special calls do not run Vyper statements, so their no-TypeError properties are finite branch boundary facts under context/account/ABI/builtin typing. Public wrappers remain split, but internal proof should use the strongest joint body-call invariant where current source permits.

#### Definition design
Introduce a local joint internal-call lemma only if both internal wrappers otherwise duplicate setup. Its conclusion should include no-TypeError, preservation, and return/exception typing. Boundary probes: argument/default binding preserves env consistency; body `ReturnException` matches declared return type. Failure sign: wrappers unfold identical setup independently.

#### Code structure
All call-specific helpers belong in `semantics/prop/vyperTypeCallSoundnessScript.sml`. Consume `vyperTypeStmtSoundness` and `vyperTypeBuiltins`; keep default/ABI helper work in dedicated theories only if local proof cannot handle it.

### C5.1: Joint internal-call body soundness lemma
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: Shared call setup facts are standard applications of statement soundness plus scope/frame helper layers.
- Dependencies: C2.7
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C5.1

#### Progress note
Prove only if current wrappers are not already one-line projections from an existing joint theorem.

#### Summary
- Prove a local joint lemma for internal callable body evaluation.
- Include no-TypeError, state/account/env preservation, and return value/exception typing.
- Apply C2 after argument/default/local-scope setup.
- Use this lemma for both internal call wrappers.

#### Statement
```sml
(* Shape follows current eval_internal_call parameters *)
... eval_internal_call ... = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\ (* preservation and return/exception typing facts *)
  ...
```

#### Approach
Unfold internal-call setup to the point where the body statements are evaluated under an extended env/scope. Apply statement soundness, then use scope-pop/frame lemmas to restore caller invariants and translate body returns to call results.

#### Not to try
Do not choose a lemma proving only no-TypeError; preservation wrapper would repeat the setup proof.

### C5.2: Derive internal call wrappers
- Kind: `compatibility_wrappers`
- Risk: 1
- Rationale: Projections from C5.1 or an existing equivalent joint theorem.
- Dependencies: C5.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C5.2

#### Progress note
Keep current theorem names and caller-compatible statements.

#### Summary
- Prove `internal_call_no_type_error`.
- Prove `internal_call_type_preservation`.
- Use the joint internal-call lemma, not body-evaluation unfolding.
- Preserve wrapper strength required by the public surface.

#### Statement
```sml
Theorem internal_call_no_type_error: ...
Theorem internal_call_type_preservation: ...
```

#### Approach
Instantiate the joint internal-call theorem with the evaluation equation and wrapper premises, then project the desired no-TypeError or preservation/result typing fields.

#### Not to try
Do not weaken wrapper statements or duplicate call setup reasoning.

### C5.3: Prove external and special call no-TypeError wrappers
- Kind: `proof_batch`
- Risk: 2
- Rationale: Finite call-entry branches under context/account/ABI/builtin facts; no recursive statement proof needed.
- Dependencies: C4.6
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C5.3

#### Progress note
Keep ABI arithmetic delegated to C4 helpers.

#### Summary
- Prove `external_call_no_type_error`.
- Prove `special_call_no_type_error`.
- Use context/account well-typedness and C4 no-TypeError boundaries.
- Runtime failures may remain possible, but not TypeError.

#### Statement
```sml
Theorem external_call_no_type_error: ...
Theorem special_call_no_type_error: ...
```

#### Approach
Unfold only the top-level external/special branch. Dispatch ABI encode/decode and builtin-like checks using C4 theorems; use account/context invariants to rule out TypeError-specific failures.

#### Not to try
Do not prove external failure impossible. Do not move ABI bound proofs into the call file.

### C5.4: Call theory build/audit checkpoint
- Kind: `checkpoint`
- Risk: 1
- Rationale: Mechanical verification after call wrappers.
- Dependencies: C5.2, C5.3
- Checkpoint: yes

#### Progress note
Ensures `vyperTypeSoundnessNew` can import trusted call wrappers.

#### Summary
- Build `vyperTypeCallSoundnessTheory`.
- Confirm no cheats remain in `vyperTypeCallSoundnessScript.sml`.
- Confirm wrapper names are available to final public surface.
- Escalate if a wrapper statement appears stronger than executable semantics.

#### Statement
```sh
holbuild build vyperTypeCallSoundnessTheory
```

#### Approach
Use build log and grep. If failure arises from body theorem shape, revisit C5.1 instead of patching wrappers separately.

#### Not to try
Do not claim final public soundness while call wrappers import or contain cheats.

### C6: Final public wrappers and zero-CHEAT reachable build
- Kind: `final_integration`
- Risk: 2
- Rationale: After C1-C5, remaining work is wrapper projection in `vyperTypeSoundnessNewScript.sml` and a mechanical reachable-build audit.
- Required for completion: yes
- Dependencies: C2, C3, C4, C5
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: PLAN_type_system_rewrite.md C6

#### Progress note
This component implements the TASK completion criterion and frozen public behavior. Wrapper names may remain source-specific but must be equivalent in strength to the six named obligations.

#### Summary
- Ensure `vyperTypeSoundnessNewScript.sml` exposes wrappers equivalent to the six public obligations named in the TASK.
- Public behavior: no well-typed evaluation returns `Error (TypeError s)` and successful/exceptional results preserve required invariants.
- Build `vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from that theory.

#### Statement
```sml
Theorem typed_stmts_no_type_error: ...
Theorem typed_stmts_success_preserves_state_env: ...
Theorem typed_stmts_exception_preserves_state_and_return_type: ...
Theorem typed_expr_no_type_error: ...
Theorem typed_expr_success_preserves_type: ...
Theorem typed_callable_body_no_type_error: ...

# Final criterion
holbuild build vyperSemanticsHolTheory
```

#### Approach
Derive public wrappers as projections/corollaries of C2 statement/expression soundness and C5 callable-body/call facts. Then run the final build and inspect warning provenance; any reachable CHEAT in fresh stack must be traced to one of C1-C5 or escalated as an uncovered current-source obligation.

#### Not to try
Do not change frozen public behavior or weaken wrapper conclusions. Do not count a clean build with CHEAT warnings as done. Do not chase unrelated retired-theory cheats unless they are reachable from `vyperSemanticsHolTheory`.

#### Argument
The final public surface is a corollary layer over the strongest joint invariants. C2 supplies no-TypeError and preservation for statements/expressions/evaluator cases; C5 supplies callable body/call wrappers; C3 supplies assignment compatibility wrappers for any legacy callers; C4 removes builtin/update-binop cheat dependencies. Therefore the named public theorems follow by instantiation and projection, and the aggregator build is trusted once the reachable import graph has no CHEAT warnings.

#### Definition design
No new semantics/type-system definitions should be introduced at final integration. If a public wrapper needs a missing projection, add a small corollary over existing joint theorems. Failure sign: a public wrapper proof unfolds evaluator definitions directly; the appropriate joint theorem/wrapper is missing upstream.

#### Code structure
Public wrappers and final compatibility names belong in `semantics/prop/vyperTypeSoundnessNewScript.sml`. The aggregator `vyperSemanticsHolScript.sml` should only import the fresh final theory; do not re-enable old retired theories.
