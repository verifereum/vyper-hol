# PLAN

## Structured Components

### C0: Reachability and current-source proof-obligation audit
- Kind: `audit`
- Risk: 1
- Rationale: Mechanical build/grep/audit work against the TASK’s authoritative current source. It does not change proof architecture and only prevents work on stale or unreachable obligations.
- Checkpoint: yes

#### Summary
- Establish the current reachable CHEAT/suspend/scaffold set before editing.
- Use `holbuild`, not direct HOL, as required by the TASK.
- Treat fresh theories reachable from `vyperSemanticsHolTheory` as in scope.
- Map every reachable unfinished obligation to C1–C9; if one does not fit, stop for augment instead of inventing work.

#### Statement
Run:
```sh
holbuild build vyperTypeStatePreservationTheory
holbuild build vyperSemanticsHolTheory
```
Then audit fresh-stack files reachable from `vyperSemanticsHolTheory` for `cheat`, `suspend`, and build-through scaffolding. Record the exact theorem/Resume names and assign each to a component below.

#### Approach
Start from the TASK-listed fresh theories, then use build output/import reachability to include only strict prerequisites. Retired `vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, and `vyperTypeSoundness` are out of scope unless the build proves they are still imported transitively.

#### Not to try
Do not perform repository-wide cleanup. Do not chase unrelated cheats merely because grep finds them; the contract is reachability from `vyperSemanticsHolTheory` in the fresh stack.

### C1: Localized builtin, binop, and type-builtin soundness
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The obligations are numerous but structurally finite case analyses over executable builtin/operator/type-builtin definitions. Known hard points such as ABI bounds and environment/account builtins are localized and can be probed before downstream work consumes them.
- Required for completion: yes
- Dependencies: C0
- Checkpoint: yes

#### Summary
- Prove all reachable unfinished obligations in `vyperTypeBuiltinsScript.sml`.
- This supplies the no-TypeError/success-typing interface consumed by expression, update-assignment, and statement soundness.
- Keep builtin reasoning local; downstream files should consume wrapper theorems, not unfold builtin semantics.
- If a runtime/typing mismatch is real, repair the internal builtin/type-builtin predicate or helper layer; do not weaken the public soundness surface.

#### Statement
Remove all reachable cheats/suspends in `semantics/prop/vyperTypeBuiltinsScript.sml`, including current-source obligations with names such as:
```sml
well_typed_binop_no_type_error
well_typed_binop_success_type
well_typed_update_binop_no_type_error
well_typed_builtin_app_no_type_error
well_typed_builtin_app_success_type
well_typed_type_builtin_no_type_error
well_typed_type_builtin_success_type
```
and any current-source resumed suspended branches of these theorems.

#### Approach
Prove binops first, then update-binop, then builtin app, then type-builtin/ABI. For each family, split on the builtin/operator constructor and use existing value/bytes/crypto/conversion/ABI lemmas where they match the branch. Keep no-TypeError and success-typing proofs mutually aligned so consumers do not need to redo constructor analysis.

#### Not to try
Do not unfold builtin semantics in assignment or statement soundness. Do not add public side conditions excluding ABI encode sizes, `MsgGas`, or other builtin cases; if a static predicate lacks a necessary executable bound, repair that internal predicate or prove a checked counterexample and escalate.

#### Argument
Builtin soundness is a finite compatibility proof between three layers: static well-typed builtin/operator predicates, executable builtin/operator functions, and `value_has_type`/runtime typing. For each constructor, the static predicate must entail every dynamic side condition needed by the executable branch, and any successful dynamic value must have the statically declared result type. No evaluator induction is needed here; the induction boundary is downstream. The important invariant is: “well-typed inputs to this builtin family cannot produce `Error (TypeError s)`, and successful outputs satisfy the declared value type.” Update-binop assignment is then only a consumer of binop soundness, not a place to re-open operator cases.

#### Definition design
The proof interface exported from `vyperTypeBuiltinsScript.sml` should consist of family-level theorems such as binop no-TypeError/success type, update-binop no-TypeError, builtin-app no-TypeError/success type, and type-builtin no-TypeError/success type. ABI/type-builtin definitions must expose any bound predicates needed by executable encoding/decoding as consequences of the static well-typed predicate. Probe failure signs: a branch needs an unprovable numeric bound, `MsgGas`/environment lookup has no typing premise, or a successful executable result has no corresponding `value_has_type` constructor. In those cases repair the internal predicate/helper exactly at the owning builtin/type-builtin layer.

#### Code structure
All proofs and any small local bridge lemmas belong in `semantics/prop/vyperTypeBuiltinsScript.sml` or the narrowly owning helper theory already imported there (`vyperTypeABIScript.sml`, bytes/crypto/conversions/defaults helpers) if the fact is reusable and semantic rather than proof-local. Do not introduce a new library file unless repeated proof code becomes an imported theorem interface. Downstream theories should import and use only the family theorems, not branch-local suspended names.

### C1.1: Binop and update-binop interface
- Kind: `proof`
- Risk: 2
- Rationale: Finite operator/value case splits; this is the known strict prerequisite for the inherited update-assignment path.
- Dependencies: C0

#### Summary
- Close binop no-TypeError and success-typing cheats.
- Close update-binop no-TypeError using binop soundness.
- Export the interface needed by assignment leaf operations.

#### Statement
Prove current-source binop/update-binop obligations, especially:
```sml
well_typed_binop_no_type_error
well_typed_binop_success_type
well_typed_update_binop_no_type_error
```

#### Approach
Case split by operator and operand value/type constructors, matching `well_typed_binop_def` and executable binop definitions. Prove success typing as the companion fact to no-TypeError because update assignment needs both dynamic non-TypeError behavior and value typing.

#### Not to try
Do not defer `well_typed_update_binop_no_type_error` by adding assumptions in assignment lemmas; C2 depends on this interface.

### C1.2: Builtin-app no-TypeError and success typing
- Kind: `proof`
- Risk: 2
- Rationale: Many branches, but each suspended branch is local to one builtin constructor and existing helper theories are intended to discharge the value-typing facts.
- Dependencies: C1.1

#### Summary
- Close current suspended builtin-app branches.
- Cover arithmetic/crypto/bytes/string/array/environment/account/special builtin constructors.
- Keep branch lemmas local unless they are semantic reusable facts.

#### Statement
Prove all reachable current-source suspended/cheated branches of:
```sml
well_typed_builtin_app_no_type_error
well_typed_builtin_app_success_type
```

#### Approach
Proceed constructor-by-constructor. For crypto/bytes/string/array branches, consume the corresponding fresh helper theorem; for environment/account branches, derive well-typed lookup/result facts from runtime/account consistency assumptions already present in the builtin predicate.

#### Not to try
Do not create a second expression soundness theorem in the builtin file. Do not leave a branch as an assumption to be supplied by statement soundness.

### C1.3: Type-builtin and ABI bound probes/proofs
- Kind: `proof`
- Risk: 2
- Rationale: The known ABI-bound issues can be reduced to small predicate-implies-bound probes before proving the finite constructor wrapper, keeping risk local.
- Dependencies: C1.1
- Checkpoint: yes

#### Summary
- Prove exact ABI/type-builtin side-condition probes.
- Close `extract32`, `abi_decode`, `abi_encode`, `encode_tuple`, and `encode_tuple_nowrap` suspended branches if reachable.
- Repair internal type-builtin predicates if a required executable bound is missing.

#### Statement
Prove all reachable current-source type-builtin no-TypeError and success-typing obligations, including ABI encode/decode/extract branches, with preliminary lemmas showing the well-typed type-builtin predicate implies every executable ABI bound required by the branch.

#### Approach
First state tiny branch probes: static type-builtin well-typedness implies the precise size/bound/shape check used by the executable ABI function. Once those probes compile, the wrapper theorem is a case split on the type-builtin constructor plus existing ABI value-typing lemmas.

#### Not to try
Do not hide ABI bounds as assumptions on public soundness wrappers. Do not use downstream expression hypotheses to patch a missing type-builtin predicate.

### C2: Assignment subscript and leaf-operation soundness
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The recursive shape follows `assign_subscripts`; after C1, update-binop is a local leaf case. Strengthened dynamic-array and assignable-type premises already address the known false branches.
- Required for completion: yes
- Dependencies: C1
- Checkpoint: yes

#### Summary
- Prove inherited update-binop-path obligations in `vyperTypeStatePreservationScript.sml`.
- Establish that typed leaf operations do not produce TypeError and preserve the expected leaf type.
- Lift leaf facts through recursive subscript assignment.
- This is a strict prerequisite for assignment-target soundness C3.

#### Statement
Remove inherited reachable cheats named in the TASK/current source, including:
```sml
assign_subscripts_update_leaf_no_type_error
assign_operation_runtime_typed_leaf_no_type_error
assign_subscripts_no_type_error_runtime_typed
assign_subscripts_preserves_type_runtime_typed
```

#### Approach
Prove the leaf-operation theorem by cases on the assignment operation. Then prove no-TypeError and preservation for `assign_subscripts` by recursion-matching induction on the executable function, carrying the leaf type and assignable/non-`None` facts through the suffix path.

#### Not to try
Do not weaken `assign_operation_runtime_typed` for `PopOp`; the dynamic-array premise is necessary. Do not unfold binop semantics in this file; use C1 theorems.

#### Argument
`assign_subscripts` recursively navigates a path and eventually applies an assignment operation at a leaf. The invariant must therefore be stated at two levels. At the leaf, `assign_operation_runtime_typed env ty op` and `assignable_type env.type_defs ty` rule out TypeError and give a value of the same runtime type when the operation succeeds. At each subscript frame, target path typing supplies a well-typed index/key and the recursive call preserves the child type; reconstructing the parent value then preserves the original type. The proof should follow the recursion of `assign_subscripts`, not the syntax of assignment statements.

#### Definition design
The consumer interface should expose: leaf-operation no-TypeError, subscript no-TypeError under runtime-typed leaf operation, and subscript type preservation under the same premises. `assign_operation_runtime_typed` is the boundary predicate: update operations consume C1 binop/update-binop soundness; append/pop must require dynamic-array facts; replace requires value type compatibility. Probe failure signs are exactly: `PopOp` on a non-dynamic array, update binop lacking success typing, or a subscript step without a key/index `value_has_type` fact.

#### Code structure
Keep these lemmas in `semantics/prop/vyperTypeStatePreservationScript.sml`, near existing assignment/subscript preservation lemmas. If a binop fact is missing, add it in `vyperTypeBuiltinsScript.sml` under C1, not here. Avoid duplicating statement-level assignment typing facts; C2 is purely runtime assignment/subscript infrastructure.

### C3: Complete `assign_target_sound_mutual`
- Kind: `mutual_theorem`
- Risk: 2
- Rationale: The theorem has already been strengthened with the side conditions identified by the handover. Remaining work is branch-local and follows the evaluator’s existing mutual recursion.
- Required for completion: yes
- Dependencies: C2
- Checkpoint: yes

#### Summary
- Finish `assign_target_sound_mutual` in `vyperTypeStatePreservationScript.sml`.
- Replace scaffolding in the TASK-listed branches: `TopLevelVar` HashMapRef, `TopLevelVar` ArrayRef, `ImmutableVar`, `TupleTargetV`, and `assign_targets` cons.
- Preserve the strengthened side conditions; do not weaken the theorem.
- Export this as the central assignment no-TypeError/preservation theorem for wrappers and statement soundness.

#### Statement
Finalize current-source theorem equivalent to:
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
with current-source names/types if they differ.

#### Approach
Prove preservation by existing all-result preservation lemmas, and prove no-TypeError by branch-specific no-TypeError facts. Split only at evaluator branch points and close each branch immediately, using exact helper lemmas for fragile `TopLevelVar` cases.

#### Not to try
Do not use broad top-level `gvs[..., AllCaseEqs(), ...]` and then clean up dozens of residual goals. Do not remove `assign_operation_matches_target_shape` or `assign_target_assignable_context`.

#### Argument
The mutual theorem follows the executable recursion of `assign_target` and `assign_targets`. For a single target, `target_runtime_typed` identifies the runtime place and expected type, `assign_operation_runtime_typed` types the operation at that leaf, `assign_operation_matches_target_shape` rules out applying tuple operations to scalar places or vice versa, and `assign_target_assignable_context` supplies runtime writability/layout facts for places that static typing alone cannot guarantee. The conclusion is all-result: even when assignment fails after partial state updates, the resulting state remains runtime-consistent and the result is not a TypeError. For target lists, the head assignment produces an intermediate state; the second conjunct’s induction hypothesis must be applied to the tail in that intermediate state, with tail premises transported by preservation/stability facts.

#### Definition design
`assign_target_assignable_context` is the boundary between statement typing/runtime target evaluation and low-level assignment. It must expose exactly: scoped assignability, top-level declaration/module-code/layout-slot success, nonempty hashmap subscript information, and componentwise tuple contexts. `assign_operation_matches_target_shape` is the boundary preventing impossible operation/target combinations. Branch helper lemmas should be exact consumers of these predicates for `HashMapRef` and `ArrayRef`; if a helper still requires unfolding statement typing, the boundary predicate is missing a fact and the executor must escalate.

#### Code structure
Keep the mutual theorem and exact branch helpers in `semantics/prop/vyperTypeStatePreservationScript.sml`. Place helper lemmas immediately before the corresponding `Resume assign_target_sound_mutual[...]` block. Do not move assignment-target proof logic into `vyperTypeAssignSoundnessScript.sml`; that file should only provide compatibility corollaries after C3.

### C3.1: TopLevelVar HashMapRef branch helper
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The handover records existing hashmap path, declaration, slot, split-subscript, and storage no-TypeError helpers. The remaining work is to package them into an exact branch lemma.
- Dependencies: C2
- Checkpoint: yes

#### Summary
- Prove an exact helper for the `lookup_global = HashMapRef ...` branch.
- Use assignable context to obtain declaration/layout/nonempty-subscript facts.
- Use target path typing to type hashmap keys and leaf suffix assignment.
- Feed C2 for recursive suffix assignment.

#### Statement
State and prove a helper matching the branch where:
```sml
lookup_global cx src n st = (INL (HashMapRef is_transient base_slot kt vt), st)
```
inside `assign_target cx (BaseTargetV (TopLevelVar src n) sbs) op st`, concluding the branch’s `runtime_consistent env cx st' /\ no_type_error_result res` under the C3 hypotheses.

#### Approach
From `assign_target_assignable_context`, obtain module-code/declaration/layout-slot success and nonempty hashmap subscript facts. Use `target_runtime_typed`/`target_path_type` facts plus split-hashmap-subscript lemmas to type the key prefix and the leaf suffix, invoke C2 on the suffix operation, and finish storage read/write no-TypeError through existing typed storage lemmas.

#### Not to try
Do not inline this proof inside `sound_TopLevelVar` before the helper statement is accepted. Do not destruct the whole global lookup with `AllCaseEqs()`.

### C3.2: TopLevelVar ArrayRef branch helper
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: Array assignment splits into a small set of executable branches: append, pop, and ordinary path update. C2 and dynamic-array premises handle the leaf work.
- Dependencies: C2
- Checkpoint: yes

#### Summary
- Prove exact helper(s) for `lookup_global = ArrayRef ...`.
- Separate append/pop from ordinary element/path update.
- Use dynamic-array facts from operation typing for append/pop.
- Use C2 for recursive subscript/path update.

#### Statement
State and prove helper(s) matching the `TopLevelVar` branch where `lookup_global` returns an `ArrayRef ...`, concluding the branch’s C3 postcondition under the C3 hypotheses.

#### Approach
Case split first on the assignment operation because append/pop have distinct dynamic-array semantics. For ordinary updates, resolve the array element/path leaf type, apply C2, then use typed storage write-back facts to close no-TypeError and preservation.

#### Not to try
Do not try to reuse the hashmap helper directly; the evaluator branch structure and dynamic-array operations differ.

### C3.3: ImmutableVar branch of assignment-target soundness
- Kind: `proof`
- Risk: 2
- Rationale: This branch has no top-level storage/hashmap layout complexity and is handled by immutable-specific consistency/setter preservation lemmas plus C2.
- Dependencies: C2

#### Summary
- Replace the `sound_ImmutableVar` scaffold.
- Use immutable runtime consistency and setter preservation lemmas.
- Use C2 for subscript/leaf updates.
- Close no-TypeError by assignment-result lemmas.

#### Statement
Complete `Resume assign_target_sound_mutual[sound_ImmutableVar]` in the current source.

#### Approach
Obtain the immutable’s current runtime type/value from runtime consistency. Apply C2 to subscript/leaf updates and use immutable setter preservation facts to restore `runtime_consistent`; no-TypeError follows from the subscript/leaf theorem plus successful assignment-result no-TypeError.

#### Not to try
Do not treat immutables as scoped locals or top-level storage variables; use immutable-specific facts.

### C3.4: TupleTargetV branch of assignment-target soundness
- Kind: `proof`
- Risk: 2
- Rationale: The strengthened shape and list packaging predicates were introduced to make this branch structural rather than index-based.
- Dependencies: C2

#### Summary
- Replace the `sound_TupleTargetV` scaffold.
- Shape matching should force replacement with aligned component values.
- Package premises for the second conjunct of the mutual theorem.
- Avoid manual `EL`/length reconstruction.

#### Statement
Complete `Resume assign_target_sound_mutual[sound_TupleTargetV]` in the current source.

#### Approach
Unfold only the boundary predicates `assign_operation_matches_target_shape_def` and `target_assignment_values_assignable_def` as needed. Use the aligned list relation to invoke the `assign_targets` induction hypothesis for component assignments.

#### Not to try
Do not reconstruct tuple/list alignment by repeated indexing; use the list relation already present in the target-assignment predicate.

### C3.5: `assign_targets` cons branch
- Kind: `proof`
- Risk: 2
- Rationale: The subtle point is state threading: the tail must be proved from the post-head state, and the first conjunct plus preservation supplies that state consistency.
- Dependencies: C3.3, C3.4

#### Summary
- Replace the `sound_assign_targets_cons` scaffold.
- Destructure head/tail list relations and `EVERY` contexts.
- Apply the head target theorem to the actual intermediate state.
- Transport tail premises across the head assignment and apply the tail IH.

#### Statement
Complete `Resume assign_target_sound_mutual[sound_assign_targets_cons]` in the current source.

#### Approach
Split `target_assignment_values_assignable`/`LIST_REL3` and `EVERY` into head and tail. Use the head IH to get `runtime_consistent env cx st1` and no-TypeError for the head result; for continuing cases, re-establish tail assignability/context stability at `st1` and apply the tail IH.

#### Not to try
Do not prove both head and tail against the original state; the evaluator recurses on the state returned by the head assignment.

### C3.6: TopLevelVar resume integration
- Kind: `integration`
- Risk: 1
- Rationale: After C3.1/C3.2, this is dispatch from the existing `TopLevelVar` proof skeleton to exact branch helpers; the Value branch is already handled by current-source work.
- Dependencies: C3.1, C3.2

#### Summary
- Complete `sound_TopLevelVar` by replacing remaining HashMapRef/ArrayRef cheats.
- Preserve the existing Value branch proof.
- Avoid new semantic decomposition after calling exact helpers.

#### Statement
Complete `Resume assign_target_sound_mutual[sound_TopLevelVar]` by replacing the remaining `HashMapRef` and `ArrayRef` scaffolding with calls to C3.1/C3.2 helpers.

#### Approach
In the `HashMapRef` and `ArrayRef` cases, instantiate the exact helper using the current branch hypotheses and conclude. Leave the proven storage `Value` branch unchanged except for any naming adjustments forced by helper placement.

#### Not to try
Do not rewrite the already-proved Value branch or expand the whole `lookup_global` computation again.

### C4: Assignment compatibility wrappers
- Kind: `corollary_cluster`
- Risk: 2
- Rationale: Once C3 is complete, legacy assignment wrappers should be projections or small compatibility corollaries. Any required strengthened premises are already named by C3.
- Required for completion: yes
- Dependencies: C3

#### Summary
- Remove reachable cheats in `vyperTypeAssignSoundnessScript.sml`.
- Turn old no-TypeError wrappers into corollaries of C3.
- Strengthen internal wrapper statements only if callers can supply the strengthened C3 premises.
- Do not re-induct over assignment targets.

#### Statement
Prove reachable current-source wrappers such as:
```sml
assign_target_no_type_error
assign_target_update_no_type_error
assign_target_append_no_type_error
```
or replace them with compatibility corollaries of equivalent downstream strength.

#### Approach
Project `no_type_error_result` from `assign_target_sound_mutual`. If a legacy wrapper has weaker assumptions, first prove that those assumptions imply `assign_operation_matches_target_shape` and `assign_target_assignable_context`; if not, strengthen the internal wrapper and update fresh-stack callers.

#### Not to try
Do not duplicate evaluator case analysis from `assign_target` or reopen hashmap/array storage branches in this file.

### C5: Statement-level assignment side-condition bridge lemmas
- Kind: `infrastructure_lemma_cluster`
- Risk: 2
- Rationale: The TASK identifies these as the exact missing statement obligations after assignment preservation was strengthened. They are structural consequences of statement typing, target evaluation typing, runtime consistency, and declaration/layout facts.
- Required for completion: yes
- Dependencies: C3, C4
- Checkpoint: yes

#### Summary
- Prove reusable bridge lemmas in `vyperTypeStmtSoundnessScript.sml` or adjacent helper layer.
- Derive `assign_operation_matches_target_shape` for assignment operations.
- Derive `assign_target_assignable_context` for evaluated targets.
- Package tuple/list assignment into `target_assignment_values_assignable` plus component contexts.
- Derive AnnAssign non-`NoneT`/non-`NoneTV` facts from `assignable_type`.

#### Statement
Prove reusable lemmas deriving:
1. `assign_operation_matches_target_shape gv op` for `AnnAssign`, `Assign`, `AugAssign`, append/pop, and tuple/list replacement;
2. `assign_target_assignable_context cx gv st` for evaluated assignment targets;
3. non-`NoneT`/non-`NoneTV` consequences needed by `AnnAssign` from `assignable_type`;
4. `target_assignment_values_assignable env cx st tgts gvs vs` and `EVERY (\gv. assign_target_assignable_context cx gv st) gvs` for tuple/list assignment.

#### Approach
Use existing expression/target evaluation soundness to obtain runtime target/value typing. For scoped targets, derive assignability from scope/env consistency; for top-level targets, use declaration lookup, module-code, storage/hashmap layout, and nonempty subscript facts. For AnnAssign use existing non-None lemmas; for tuple/list use induction over the existing aligned relation.

#### Not to try
Do not unfold `assign_target_def` in statement proofs. Do not add local assumptions for C3 side conditions in `eval_all_type_sound_mutual`; prove bridge lemmas that derive them.

#### Argument
Statement typing reasons about syntax, evaluated targets, and RHS values; assignment-target soundness C3 reasons about runtime assignment places and operation predicates. C5 is the bridge. For scalar assignment branches, statement typing plus expression/target evaluation soundness gives a runtime-typed target/value pair, from which shape and operation typing are immediate. For top-level places, runtime consistency connects static declarations to module code, storage layout, hashmap slots, and writability; this is exactly `assign_target_assignable_context`. For tuple/list assignment, the proof must preserve component alignment as a list relation so that C3’s `assign_targets` conjunct can consume it directly.

#### Definition design
The desired boundary lemmas should conclude the exact predicates consumed by C3: `assign_operation_matches_target_shape`, `assign_target_assignable_context`, `target_assignment_values_assignable`, and `EVERY (\gv. assign_target_assignable_context cx gv st) gvs`. They should not expose `assign_target_def`. Failure signs: a lemma needs to assume a top-level slot/layout fact not derivable from runtime consistency and target typing; a tuple proof degenerates into manual length arithmetic; or AnnAssign requires a naked `ty <> NoneT` assumption instead of deriving it from `assignable_type`. Escalate on those signs.

#### Code structure
Put statement-specific bridge lemmas near the assignment cases in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. If a bridge is generally about static env extension or scope-frame consistency, place it in the existing owning theory (`vyperTypeEnvExtension`, `vyperTypeEnvPreservation`, or `vyperTypeScopePop`) only when needed by multiple files. Do not move low-level assignment lemmas out of `vyperTypeStatePreservationScript.sml`.

### C5.1: Shape side-condition lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: Shape matching is a finite consequence of operation and evaluated target-value constructors, with tuple/list alignment supplied by the statement typing/materialization relation.
- Dependencies: C3

#### Summary
- Prove operation-specific shape lemmas.
- Base targets close by simplification or base-shape facts.
- Tuple replacement uses aligned component-list facts.
- Append/pop/update use operation-specific typing premises.

#### Statement
Prove lemmas concluding:
```sml
assign_operation_matches_target_shape gv op
```
from the evaluated target/value facts available in statement assignment branches.

#### Approach
Split by assignment operation and target-value constructor. For tuple/list replacement, use the materialized RHS/component relation to establish matching length/alignment; for scalar operations, the shape predicate should reduce directly.

#### Not to try
Do not infer tuple length by ad hoc `EL` arithmetic if a list relation is present.

### C5.2: Assignable-context side-condition lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The predicate was introduced to name exactly the runtime writability facts needed by C3. Scoped and top-level cases are finite but require careful use of runtime consistency.
- Dependencies: C3
- Checkpoint: yes

#### Summary
- Prove assignable context for evaluated targets.
- Scoped variables use scope lookup assignability.
- Top-level variables use module/declaration/layout consistency.
- Tuple targets use componentwise `EVERY`.

#### Statement
Prove lemmas concluding:
```sml
assign_target_assignable_context cx gv st
```
for runtime target values `gv` produced by well-typed assignment-target evaluation under `runtime_consistent env cx st`.

#### Approach
Proceed by target-value structure. Scoped cases use env/scope consistency and assignability preservation of target evaluation. Top-level storage/hashmap/array cases use declaration lookup, module code, layout-slot success, and nonempty subscript/key facts from target path typing. Tuple cases map the lemma over components.

#### Not to try
Do not replace this with assumptions in statement branch proofs; C3 call sites must derive the predicate.

### C5.3: AnnAssign assignable-type consequences
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: The durable plan records existing lemmas `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV`; this is wiring.
- Dependencies: C3

#### Summary
- Derive `ty <> NoneT` and evaluated type not `NoneTV` for AnnAssign.
- Use existing assignable-type lemmas.
- Keep results as small rewrite/drule helpers for statement branches.

#### Statement
Prove any missing current-source helper lemmas that derive non-`NoneT` and evaluated non-`NoneTV` facts from:
```sml
assignable_type env.type_defs ty
```
and type-evaluation hypotheses used by AnnAssign.

#### Approach
Apply `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV` directly. Phrase helpers to match the residual AnnAssign goals in `eval_all_type_sound_mutual`.

#### Not to try
Do not add `ty <> NoneT` as a new statement-soundness hypothesis.

### C5.4: Tuple/list assignment packaging
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The target-assignment relation is the intended input to `assign_targets`; a structural list proof avoids redoing alignment at the C3 call site.
- Dependencies: C5.1, C5.2, C5.3

#### Summary
- Package component target/value typing into C3’s list predicate.
- Also prove componentwise assignable contexts.
- Use the existing aligned list relation rather than indices.
- This supplies tuple/list assignment branches in C6.

#### Statement
Prove lemmas packaging typed target lists, materialized RHS values, and assignable contexts into:
```sml
target_assignment_values_assignable env cx st tgts gvs vs /\
EVERY (\gv. assign_target_assignable_context cx gv st) gvs
```

#### Approach
Induct over the aligned target/value/materialization relation already used by the statement typing/evaluation branch. The head case uses C5.1–C5.3 and the tail case keeps the same pre-assignment state until `assign_targets` begins.

#### Not to try
Do not prove this with repeated `EL`/`LENGTH` reasoning unless the source relation is explicitly indexed.

### C6: Assignment cases of `eval_all_type_sound_mutual`
- Kind: `mutual_theorem_cases`
- Risk: 2
- Rationale: After C5, the assignment branches are integration: expression/target evaluation gives typed runtime inputs, bridge lemmas derive C3 side conditions, and C3/C4 provides assignment soundness.
- Required for completion: yes
- Dependencies: C1, C2, C3, C4, C5
- Checkpoint: yes

#### Summary
- Remove assignment-related cheats/scaffolding in `vyperTypeStmtSoundnessScript.sml`.
- Cover `AnnAssign`, `Assign`, `AugAssign`, tuple/list assignment, append/pop, and update assignment branches identified by C0.
- Feed strengthened assignment side conditions to C3/C4.
- Stay inside the existing joint evaluator invariant.

#### Statement
Complete all assignment-related current-source branches of `eval_all_type_sound_mutual`, especially:
```sml
eval_all_type_sound_mutual[AnnAssign]
eval_all_type_sound_mutual[Assign]
eval_all_type_sound_mutual[AugAssign]
```
and tuple/list, append/pop, and update-assignment branches found by C0.

#### Approach
Follow evaluator order: evaluate target(s), evaluate RHS/materialized values, derive runtime typing and assignability facts, build `assign_operation_runtime_typed`, shape, and assignable-context premises using C5, then invoke C3 or C4. `AugAssign` consumes C1/C2 through update-binop and leaf/subscript update soundness.

#### Not to try
Do not unfold `assign_target_def` in `eval_all_type_sound_mutual`. Do not create a separate assignment no-TypeError induction outside the existing mutual theorem.

### C7: Remaining evaluator mutual cases in statement/expression layer
- Kind: `mutual_theorem_cases`
- Risk: 2
- Rationale: The final public wrappers depend on the existing joint evaluator theorem having no suspended cases. Once builtin and assignment layers are complete, remaining cases are local consumers of fresh-stack env/scope/expression infrastructure.
- Required for completion: yes
- Dependencies: C1, C6
- Checkpoint: yes

#### Summary
- Remove any remaining reachable cheats/suspends inside `eval_all_type_sound_mutual` not covered by C6.
- Include statement-list, loop/iterator, target, expression, and expression-list branches only if C0 shows they are reachable/current.
- Use existing env-extension, env-preservation, scope-pop, builtin, and assignment interfaces.
- Strengthen the existing joint invariant if a downstream property is missing; do not fork a parallel proof.

#### Statement
Complete all current-source unfinished branches inside `semantics/prop/vyperTypeStmtSoundnessScript.sml`’s evaluator mutual theorem(s) that are reachable from `vyperSemanticsHolTheory` and not assignment branches covered by C6.

#### Approach
For each branch, consume the layer theorem matching the evaluator call: expression/target soundness for expression/target branches, scope-pop and env preservation for scoped blocks/loops, C1 builtin soundness for builtin expressions, and C6 assignment soundness for assignment statements. Preserve the all-result invariant through the evaluator’s real recursive calls.

#### Not to try
Do not create standalone `*_no_type_error` induction trees over the same evaluator. Do not prove call-entry setup here if the branch belongs in C8.

### C8: Call and callable-body soundness wrappers
- Kind: `corollary_cluster`
- Risk: 2
- Rationale: The TASK lists call wrappers as reachable older obligations. After statement soundness, these should be call-entry setup plus projections, not a new evaluator induction.
- Required for completion: yes
- Dependencies: C7
- Checkpoint: yes

#### Summary
- Remove reachable cheats in `vyperTypeCallSoundnessScript.sml`.
- Cover internal, external, special call no-TypeError and internal-call preservation wrappers.
- Cover callable-body wrapper needed by the public surface.
- Use statement soundness plus argument/default/env/scope setup lemmas.

#### Statement
Prove reachable current-source call wrappers, including:
```sml
internal_call_no_type_error
internal_call_type_preservation
external_call_no_type_error
special_call_no_type_error
```
and any callable-body wrapper required by `typed_callable_body_no_type_error`.

#### Approach
Prove narrow setup lemmas for argument/default value typing, function signature lookup, environment extension, account/runtime consistency, and pushed-scope/pop restoration. Invoke the completed statement/callable-body joint soundness theorem and project no-TypeError or preservation conclusions.

#### Not to try
Do not build separate call no-TypeError and call preservation induction trees. Do not weaken call wrappers by adding preconditions not implied by the fresh static call typing relation.

### C9: Public fresh surface and final zero-CHEAT build
- Kind: `final_verification`
- Risk: 1
- Rationale: After upstream reachable cheats are removed, this is projection and audit. The TASK freezes public behavior but allows internal helper theorem changes.
- Required for completion: yes
- Dependencies: C4, C7, C8
- Checkpoint: yes

#### Summary
- Ensure `vyperTypeSoundnessNewScript.sml` exposes the frozen public behavior.
- Provide compatibility corollaries if internal theorem names/statements changed.
- Run final `holbuild build vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.

#### Statement
Ensure `semantics/prop/vyperTypeSoundnessNewScript.sml` exposes wrappers equivalent in strength to:
```sml
typed_stmts_no_type_error
typed_stmts_success_preserves_state_env
typed_stmts_exception_preserves_state_and_return_type
typed_expr_no_type_error
typed_expr_success_preserves_type
typed_callable_body_no_type_error
```
Then verify:
```sh
holbuild build vyperSemanticsHolTheory
```
succeeds with zero reachable CHEAT warnings.

#### Approach
Keep the public file as a projection layer from the completed joint theorems. If internal statements were strengthened or renamed, add compatibility corollaries of equivalent public strength and update imports. Finish with a reachable-cheat audit tied back to C0.

#### Not to try
Do not weaken the frozen public behavior. Do not claim completion from a successful build if HOL reports reachable CHEAT warnings.
