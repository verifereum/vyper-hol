# PLAN

## Structured Components

### C0: Reachability and current-source obligation audit
- Kind: `audit`
- Risk: 1
- Rationale: Mechanical build/grep/audit step against the TASK’s authoritative current source; it prevents stale or unreachable work and does not decide proof architecture.
- Checkpoint: yes

#### Summary
- Establish the current reachable CHEAT/suspend/scaffold set before proof edits.
- Use `holbuild`, not direct HOL.
- Treat fresh theories reachable from `vyperSemanticsHolTheory` as in scope.
- Map every reachable unfinished obligation to C1–C9; if a reachable fresh-stack obligation does not fit, stop and request an augment plan.

#### Statement
Run:
```sh
holbuild build vyperTypeStatePreservationTheory
holbuild build vyperSemanticsHolTheory
```
Then audit fresh-stack files reachable from `vyperSemanticsHolTheory` for `cheat`, `suspend`, and build-through scaffolding. Record exact theorem/Resume names and assign each to the components below.

#### Approach
Start from the TASK-listed fresh theories and include only strict prerequisites shown by imports/build reachability. Retired `vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, and `vyperTypeSoundness` are out of scope unless the build proves they are still imported transitively.

#### Not to try
Do not perform repository-wide cleanup. Do not chase unrelated cheats merely because grep finds them; scope is reachability from `vyperSemanticsHolTheory` in the fresh stack.

### C1: Localized builtin, binop, type-builtin, and ABI soundness
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The obligations are numerous but structurally finite case analyses over executable builtin/operator/type-builtin definitions. Known hard points such as ABI bounds and environment/account builtins are localized and are handled by low-risk probes before wrappers consume them.
- Required for completion: yes
- Dependencies: C0
- Checkpoint: yes

#### Summary
- Remove all reachable unfinished obligations in `vyperTypeBuiltinsScript.sml`.
- Supply the no-TypeError/success-typing interface consumed by expression, update-assignment, and statement soundness.
- Keep builtin reasoning local; downstream theories should use wrapper theorems and not unfold builtin semantics.
- If a runtime/typing mismatch is real, repair the internal builtin/type-builtin predicate or close a checked probe before changing architecture.

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
and current-source suspended branches such as unary ops, crypto, bytes/string, array constructors, environment/account builtins, EC/powmod, and ABI encode/decode/extract branches.

#### Approach
Prove binops first, then update-binop, then builtin app, then type-builtin/ABI. For each family, split on the builtin/operator constructor and use existing value/bytes/crypto/conversion/ABI lemmas where they match the branch. Keep no-TypeError and success-typing proofs aligned so consumers do not repeat constructor analysis.

#### Not to try
Do not unfold builtin semantics in assignment or statement soundness. Do not add public side conditions excluding ABI encode sizes, `MsgGas`, or other builtin cases; if a static predicate lacks a necessary executable bound, repair that internal predicate or prove a checked counterexample and escalate.

#### Argument
Builtin soundness is a finite compatibility proof between static well-typed builtin/operator predicates, executable builtin/operator functions, and `value_has_type`/runtime typing. For each constructor, the static predicate must entail every dynamic side condition needed by the executable branch, and any successful dynamic value must have the statically declared result type. No evaluator induction is needed here; the induction boundary is downstream. The invariant is: well-typed inputs to this builtin family cannot produce `Error (TypeError s)`, and successful outputs satisfy the declared value type. Update-binop assignment is then a consumer of binop soundness, not a place to re-open operator cases.

#### Definition design
The proof interface exported from `vyperTypeBuiltinsScript.sml` should consist of family-level theorems: binop no-TypeError/success type, update-binop no-TypeError, builtin-app no-TypeError/success type, and type-builtin no-TypeError/success type. ABI/type-builtin definitions must expose any bound predicates needed by executable encoding/decoding as consequences of static well-typedness. Failure signs: a branch needs an unprovable numeric bound, `MsgGas`/environment lookup has no typing premise, or a successful executable result has no corresponding `value_has_type` constructor. In those cases repair the internal predicate/helper at the owning builtin/type-builtin layer.

#### Code structure
All proofs and small local bridge lemmas belong in `semantics/prop/vyperTypeBuiltinsScript.sml` or the narrowly owning helper theory already imported there (`vyperTypeABIScript.sml`, bytes/crypto/conversions/defaults helpers) if the fact is reusable and semantic rather than proof-local. Do not introduce a new library file unless repeated proof code becomes an imported theorem interface. Downstream theories should import and use only family theorems, not branch-local suspended names.

### C1.1: Binop and update-binop interface
- Kind: `proof`
- Risk: 2
- Rationale: Finite operator/value case split; it is the strict prerequisite for inherited update-assignment path obligations.
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
- Rationale: Many branches, but each suspended branch is local to one builtin constructor and existing helper theories are intended to discharge value-typing facts.
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
- This is a strict prerequisite for assignment-target soundness without reachable cheats.

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
`assign_subscripts` recursively navigates a path and eventually applies an assignment operation at a leaf. The invariant is two-level. At the leaf, `assign_operation_runtime_typed env ty op` and `assignable_type env.type_defs ty` rule out TypeError and give a value of the same runtime type on success. At each subscript frame, target path typing supplies a well-typed index/key and the recursive call preserves the child type; reconstructing the parent value then preserves the original type. The proof should follow `assign_subscripts` recursion, not assignment-statement syntax.

#### Definition design
The consumer interface should expose: leaf-operation no-TypeError, subscript no-TypeError under runtime-typed leaf operation, and subscript type preservation under the same premises. `assign_operation_runtime_typed` is the boundary predicate: update operations consume C1 binop/update-binop soundness; append/pop require dynamic-array facts; replace requires value type compatibility. Failure signs are exactly: `PopOp` on a non-dynamic array, update binop lacking success typing, or a subscript step without a key/index `value_has_type` fact.

#### Code structure
Keep these lemmas in `semantics/prop/vyperTypeStatePreservationScript.sml`, near existing assignment/subscript preservation lemmas. If a binop fact is missing, add it in `vyperTypeBuiltinsScript.sml` under C1, not here. Avoid duplicating statement-level assignment typing facts; C2 is purely runtime assignment/subscript infrastructure.

### C3: Complete `assign_target_sound_mutual`
- Kind: `mutual_theorem`
- Risk: 2
- Rationale: All high-risk semantic questions have been decomposed into exact branch helpers and context-extraction adapters. Remaining work is standard branch closure under the strengthened side conditions; no theorem weakening is planned.
- Required for completion: yes
- Dependencies: C2
- Checkpoint: yes

#### Summary
- Finish `assign_target_sound_mutual` in `vyperTypeStatePreservationScript.sml`.
- Replace scaffolding in the TASK-listed branches: `TopLevelVar` HashMapRef, `TopLevelVar` ArrayRef, `ImmutableVar`, `TupleTargetV`, and `assign_targets` cons.
- Preserve strengthened side conditions: `assign_operation_matches_target_shape` and `assign_target_assignable_context`.
- Export this as the central assignment no-TypeError/preservation theorem for wrappers and statement soundness.

#### Statement
Finalize the current-source theorem equivalent to:
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
using exact current-source names/types if they differ.

#### Approach
Prove preservation by existing all-result preservation lemmas and prove no-TypeError by branch-specific no-TypeError facts. Split only at evaluator branch points and close each branch immediately, using exact helper lemmas for fragile `TopLevelVar` cases.

#### Not to try
Do not use broad top-level `gvs[..., AllCaseEqs(), ...]` followed by cleanup of many residual goals. Do not remove `assign_operation_matches_target_shape` or `assign_target_assignable_context`. Do not duplicate evaluator recursion in a parallel theorem.

#### Argument
The mutual theorem follows the executable recursion of `assign_target` and `assign_targets`. For a single target, `target_runtime_typed` identifies the runtime place and expected type, `assign_operation_runtime_typed` types the operation at that leaf, `assign_operation_matches_target_shape` rules out applying tuple operations to scalar places or vice versa, and `assign_target_assignable_context` supplies runtime writability/layout facts that static typing alone cannot guarantee. The conclusion is all-result: even when assignment fails after partial state updates, the resulting state remains runtime-consistent and the result is not a TypeError. For target lists, the head assignment produces an intermediate state; the tail proof must use preservation/stability facts to transport tail premises to that intermediate state.

#### Definition design
`assign_target_assignable_context` is the boundary between statement typing/runtime target evaluation and low-level assignment. It must expose exactly: scoped assignability, top-level declaration/module-code/layout-slot success, nonempty hashmap subscript information, and componentwise tuple contexts. `assign_operation_matches_target_shape` is the boundary preventing impossible operation/target combinations. Branch helper lemmas should be exact consumers of these predicates for `HashMapRef` and `ArrayRef`; if a helper still requires unfolding statement typing, the boundary predicate is missing a fact and the executor must escalate.

#### Code structure
Keep the mutual theorem and exact branch helpers in `semantics/prop/vyperTypeStatePreservationScript.sml`. Place helper lemmas immediately before the corresponding `Resume assign_target_sound_mutual[...]` block or before the exact wrapper theorem they support. Do not move assignment-target proof logic into `vyperTypeAssignSoundnessScript.sml`; that file should provide compatibility corollaries after C3.

### C3.1: TopLevelVar no-TypeError wrapper via context-extraction adapters
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The semantic boundary lemmas for storage/hashmap/array branches are intended to match evaluator branches; the repeated failure mode is proof-engineering from expanding `assign_target_assignable_context` too late. Local adapters isolate that expansion.
- Dependencies: C2
- Checkpoint: yes

#### Summary
- Prove the exact `assign_target_TopLevelVar_no_type_error` theorem by splitting on `vtype` constructors and dispatching to branch boundary lemmas.
- Add local adapters extracting stable declaration, code, slot, and root-type witnesses from `assign_target_assignable_context`.
- The `Type` adapter returns `StorageVarDecl` facts; the `HashMapT` adapter returns `HashMapVarDecl` facts and base assignability.
- The final exact theorem should not unfold `assign_target_assignable_context`.

#### Statement
Prove or repair the current-source theorem:
```sml
Theorem assign_target_TopLevelVar_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME vt ==>
  target_path_type env vt sbs (Type ty) ==>
  assignable_type env.type_defs ty ==>
  assign_operation_runtime_typed env ty op ==>
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
  assign_target_assignable_context cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
  env.type_defs = get_tenv cx ==>
  well_formed_vtype env.type_defs vt ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Proceed bottom-up: prove clean context adapters; prove `Type` and `HashMapT` specialized wrappers using `irule` on operational boundary lemmas; then prove the exact theorem by `Cases_on vt`. Use explicit premise filling (`qexists_tac`, `goal_assum`, rewriting with `env.type_defs = get_tenv cx`) rather than global `metis_tac` through expanded context definitions.

#### Not to try
Do not expand `assign_target_assignable_context_def` in the final exact theorem. Do not use one large `metis_tac` over branch lemmas after context expansion; this is the known brittle failure mode. Do not rewrite the already-proved storage `Value` branch in the mutual theorem unless helper names force minor adjustment.

### C3.1.1: Type TopLevelVar context adapter
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: Direct unfolding of `assign_target_assignable_context_def` for `TopLevelVar`, followed by one declaration case split; existing consistency lemmas eliminate the wrong declaration constructor.
- Dependencies: C2

#### Summary
- Add a local adapter for the `Type t` vtype case.
- It returns module code, `StorageVarDecl`, slot, evaluated root type, `typ = t`, and root well-formedness witnesses.
- It is the only place in the Type path that unfolds `assign_target_assignable_context_def`.

#### Statement
Add a local theorem with this shape:
```sml
Theorem TopLevelVar_Type_assignable_context_imp_StorageVarDecl_facts[local]:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) ==>
  env.type_defs = get_tenv cx ==>
  assign_target_assignable_context cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
  ?code is_transient typ id_str slot root_tv.
    get_module_code cx src_id_opt = SOME code /\
    find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ,id_str) /\
    lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME root_tv /\
    typ = t /\
    well_formed_type_value root_tv
```

#### Approach
Unfold the context assumption with `assign_target_assignable_context_def` and `assign_target_assignable_def`, decompose declaration pairs, and split the declaration constructor. Close the `HashMapVarDecl` branch with `top_level_Type_not_hashmap_decl`; in the storage branch turn `IS_SOME` facts into concrete witnesses and use `top_level_Type_storage_decl` plus `evaluate_type_well_formed_type_value`.

#### Not to try
Do not make this lemma prove no-TypeError. Do not leave `IS_SOME` facts in the conclusion; consumers need stable `SOME` equalities.

### C3.1.2: HashMapT TopLevelVar context adapter
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: Symmetric adapter for hashmap vtype; the context definition already contains module/declaration/slot facts and base assignability.
- Dependencies: C2

#### Summary
- Add a local adapter for the `HashMapT kt vt` vtype case.
- It returns `HashMapVarDecl`, slot, module code, and `assign_target_assignable` facts.
- It hides destructive context unfolding from hashmap branch consumers.

#### Statement
Add a local theorem with this shape:
```sml
Theorem TopLevelVar_HashMapT_assignable_context_imp_HashMapVarDecl_facts[local]:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (HashMapT kt vt) ==>
  assign_target_assignable_context cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
  ?code is_transient id_str slot.
    assign_target_assignable (BaseTargetV (TopLevelVar src_id_opt id) sbs) st /\
    get_module_code cx src_id_opt = SOME code /\
    find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
    lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot
```

#### Approach
Unfold the context once, preserve the first conjunct as the returned base assignability fact, split the declaration pair, and close the `StorageVarDecl` branch with `top_level_HashMapT_not_storage_decl`. Package concrete slot/module/declaration witnesses in the `HashMapVarDecl` branch.

#### Not to try
Do not rederive or use `sbs <> []` downstream unless a boundary theorem explicitly asks for it. Do not prove this by global `metis_tac` after unfolding; use direct case analysis.

### C3.2: TopLevelVar HashMapRef and ArrayRef branch helpers
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The branches are semantically localized. HashMapRef consumes hashmap declaration/path-key invariants; ArrayRef splits into append, pop, and ordinary path update. C2 supplies recursive suffix assignment facts.
- Dependencies: C2, C3.1.1, C3.1.2
- Checkpoint: yes

#### Summary
- Prove exact helper(s) for `lookup_global = HashMapRef ...` and `lookup_global = ArrayRef ...`.
- HashMapRef uses static declaration/slot facts and strengthened hashmap key path typing.
- ArrayRef separates append/pop from ordinary element/path update.
- Helpers should conclude the branch no-TypeError/postcondition under C3 hypotheses.

#### Statement
State and prove helper(s) matching the `TopLevelVar` evaluator branches where `lookup_global` returns `HashMapRef ...` or `ArrayRef ...`, concluding `no_type_error_result res` and any C3 branch preservation facts required by the current mutual proof skeleton.

#### Approach
For HashMapRef, use context assignability to obtain module/declaration/slot facts, target path typing to justify hashmap prefix traversal, then apply `assign_subscripts_no_type_error_runtime_typed` and typed storage write-back. For ArrayRef, case split on assignment operation: append/pop use dynamic-array facts from operation typing; ordinary updates resolve the array element/path and then use C2 plus storage write-back facts.

#### Not to try
Do not prove these inline inside `sound_TopLevelVar`. Do not reuse hashmap proof structure for ArrayRef append/pop; their evaluator branches differ.

### C3.3: ImmutableVar branch of assignment-target soundness
- Kind: `proof`
- Risk: 2
- Rationale: This branch has no top-level storage/hashmap layout complexity; immutable-specific consistency/setter preservation lemmas plus C2 match the branch.
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
- Rationale: The strengthened shape and list packaging predicates were introduced so this branch is structural rather than index-based.
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
- Rationale: The subtle point is state threading: the tail must be proved from the post-head state, and the head conjunct plus preservation supplies that state consistency.
- Dependencies: C3.3, C3.4

#### Summary
- Replace the `sound_assign_targets_cons` scaffold.
- Destructure head/tail list relations and `EVERY` contexts.
- Apply the head target theorem to the actual intermediate state.
- Transport tail premises across the head assignment and apply the tail IH.

#### Statement
Complete `Resume assign_target_sound_mutual[sound_assign_targets_cons]` in the current source.

#### Approach
Split `target_assignment_values_assignable`/aligned list premises and `EVERY` into head and tail. Use the head IH to get `runtime_consistent env cx st1` and no-TypeError for the head result; for continuing cases, re-establish tail assignability/context stability at `st1` and apply the tail IH.

#### Not to try
Do not prove both head and tail against the original state; the evaluator recurses on the state returned by the head assignment.

### C3.6: TopLevelVar resume integration
- Kind: `integration`
- Risk: 1
- Rationale: After C3.1/C3.2 this is dispatch from the existing proof skeleton to exact branch helpers; the storage Value branch is already handled by current-source work.
- Dependencies: C3.1, C3.2

#### Summary
- Complete `sound_TopLevelVar` by replacing remaining HashMapRef/ArrayRef cheats.
- Preserve the existing Value branch proof.
- Avoid new semantic decomposition after calling exact helpers.

#### Statement
Complete `Resume assign_target_sound_mutual[sound_TopLevelVar]` by replacing remaining `HashMapRef` and `ArrayRef` scaffolding with calls to C3.1/C3.2 helpers.

#### Approach
In the `HashMapRef` and `ArrayRef` cases, instantiate the exact helper using the current branch hypotheses and conclude. Leave the proved storage `Value` branch unchanged except for naming adjustments forced by helper placement.

#### Not to try
Do not rewrite the already-proved Value branch or expand the whole `lookup_global` computation again.

### C4: Assignment compatibility wrappers
- Kind: `corollary_cluster`
- Risk: 2
- Rationale: Once C3 is complete, legacy assignment wrappers should be projections or small compatibility corollaries; no evaluator recursion is needed.
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
- Rationale: The previous C5.4 blocker identified a real missing static-writability invariant for TopLevelVar targets. This augmentation keeps all already-proved C5 bridge work, replaces the stuck tuple/list packaging path with a narrow typing/context repair for TopLevelNameTarget assignability, and removes/proves the only local cheated bridge theorem in the C5 helper block.
- Required for completion: yes
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0114, E0115, E0116, E0120, E0121, E0122, E0123, E0124

#### Progress note
C5.1-C5.3 progress remains valid. E0124 is accepted as evidence that env_context_consistent alone was too weak; the current plan resolves that blocker by making top-level assignment targets statically writable rather than trying to derive code/layout facts from mere FLOOKUP entries.

#### Summary
- C5 supplies the statement-level side conditions required by strengthened assignment soundness: operation shape and assignable context.
- Existing C5.2 static-context definitions and INL-success bridges are carried forward.
- The C5.4 stuck point is repaired by making TopLevelNameTarget assignment typing exclude immutable top-level entries and by strengthening env_context_consistent with code/declaration/layout existence for assignable top-level storage/hashmap entries.
- The unused cheated generic INL bridge in the C5 helper block must be deleted or replaced by a proved base-target theorem so no CHEAT warning remains.
- After this subtree, Assign/AnnAssign/AugAssign branches can call assignment no-TypeError lemmas without ad hoc TopLevelVar reasoning.

#### Description
Stay inside the C5 subtree and strict helper outputs needed by it. Edits may touch `vyperTypeSystemScript.sml` only for the narrow static-target/context interface described in C5.4.1, and `vyperTypeStmtSoundnessScript.sml` for C5 helper lemmas and local statement-branch wiring. Do not start broader builtin/call/statement proof work under this component.

#### Approach
First repair the static boundary, then re-run the C5 helper proofs that consume it. Finally audit the C5 block for remaining cheats and replace the Assign/Tuple packaging holes with calls to the named bridges.

#### Not to try
Do not try to prove `get_module_code`/layout facts from the old `env_context_consistent_def`; E0124 showed this is exactly the missing invariant. Do not weaken `assign_target_no_type_error` by dropping `assign_target_assignable_context`, because assignment really can return TypeError when static target writability is absent.

#### Argument
The assignment no-TypeError lemmas require two static side conditions: `assign_operation_matches_target_shape gv op` and `assign_target_assignable_context cx gv st`. Shape is already a syntactic consequence of the assignment operation and target/value typing. Assignable context has two parts: dynamic scoped-variable assignability, which follows from target evaluation/runtime typing and existing scope consistency, and static top-level writability, which cannot be recovered from `FLOOKUP env.toplevel_vtypes` alone.

The repair is to make the static typing/context boundary state exactly what assignment needs. `TopLevelNameTarget` as an assignment target should denote writable storage/hashmap locations, not immutable top-level names. Therefore `type_place_target` must reject `TopLevelNameTarget (src,id)` when `(src,string_to_num id)` is present in `env.bare_globals`, while expression typing may still read those names through the existing top-level expression path. Then `env_context_consistent` must guarantee that every non-bare-global `Type` entry in `env.toplevel_vtypes` has a storage declaration, evaluable type, and layout slot, and that every `HashMapT` entry has a hashmap declaration and layout slot. With those facts, the `TopLevelVar` branch of `assignment_value_static_assignable_context` follows by cases on the root vtype; the required `sbs <> []` for hashmaps follows from `target_path_type`/subscript typing because a typed assignment target of ordinary value type can only pass through a hashmap by consuming at least one subscript.

Tuple/list assignment then packages component obligations by `LIST_REL3`/`EVERY` reasoning over target runtime typing and the static-context predicate; it should not re-open evaluator case analysis. The invariant is: after successful target evaluation of a well-typed assignment target, every produced assignment value is runtime typed and, under the repaired static context boundary, has `assignment_value_static_assignable_context`; C5.2.3 converts this to `assign_target_assignable_context`.

#### Definition design
`assignment_value_static_assignable_context` remains the C5-local boundary predicate for the cx-dependent part of `assign_target_assignable_context`. Its proof interface should stay constructor-oriented: ScopedVar and ImmutableVar simplify to `T`; TupleTargetV rewrites to `EVERY`; TopLevelVar rewrites to the existential over `get_module_code`, `find_var_decl_by_num`, `evaluate_type`, and `lookup_var_slot_from_layout`.

The static type-system repair should provide two consumer lemmas rather than forcing statement proofs to unfold `env_context_consistent_def`: one for storage `Type ty` top-level target entries, and one for `HashMapT kt vt` entries. Failure signs: if a proof still attempts to infer `get_module_code cx src = SOME code` from only `FLOOKUP env.toplevel_vtypes ...`, the boundary is still too weak; if immutable/bare-global top-level targets remain well-typed assignment targets, the public no-TypeError theorem is still suspect.

Do not add cx-dependent checks directly to `type_place_target`; it only has `env`. Use the static env split: `type_place_target` rejects bare-global/immutable entries using `env.bare_globals`, and `env_context_consistent` relates the remaining top-level target entries to cx code/layout facts.

#### Code structure
- In `vyperTypeSystemScript.sml`, make the narrow definition changes for `type_place_target` and `env_context_consistent_def` near their existing definitions. Keep the new clauses close to the current top-level-vtype clauses.
- In the same or immediately downstream env helper file, add small projection lemmas for the new env-context clauses if direct unfolding becomes noisy. Prefer named lemmas over repeated `fs[env_context_consistent_def]` in statement proofs.
- In `vyperTypeStmtSoundnessScript.sml`, keep C5 helper lemmas in the existing C5 block around lines 104-323. Delete or prove the unused cheated generic INL bridge before proceeding to statement branches.
- Do not move assignment preservation theorems between files in this component; C5 only supplies side-condition bridges consumed by statement assignment cases.

### C5.1: Shape side-condition lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: Shape matching is a finite consequence of the operation constructor and target-value shape; prior evidence confirms the Replace case is already covered by `assign_operation_matches_target_shape_Replace_from_typed`.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0121

#### Progress note
No change from prior C5 plan; keep existing theorem as the statement-level shape boundary.

#### Summary
Carry forward the existing operation-shape side-condition path. For Replace assignments, use `assign_operation_matches_target_shape_Replace_from_typed`. Tuple/list Replace shape is length equality against `ArrayV (TupleV vs)`. This component should not unfold evaluator definitions.

#### Statement
Use existing theorem:
```sml
assign_operation_matches_target_shape_Replace_from_typed
```
as the boundary lemma for statement Replace assignment branches.

#### Approach
Apply the existing theorem at statement call sites after target/value typing has identified the evaluated target and replacement value. For tuple targets, rely on the theorem's built-in length/shape conclusion rather than proving a separate list lemma.

#### Not to try
Do not prove shape by expanding `assign_target_def`; shape is a precondition about the evaluated target and operation, not about assignment execution.

### C5.2: Assignable-context bridge lemmas for statement assignment
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The already-proved C5.2.1-C5.2.4 lemmas are valid and useful. The only remaining issue in this cluster is the unused cheated generic INL bridge, which is now handled explicitly by C5.2.5.
- Dependencies: C5.4.1
- Progress transition: `refinement`
- Carries progress/evidence from: E0114, E0115, E0116, E0120, E0122

#### Progress note
Prior C5.2 definitions and static/runtime bridge carry forward; C5.2.5 is revised from an optional unused cheat into a mandatory no-CHEAT cleanup.

#### Summary
- Keep `assignment_value_static_assignable_context` and its constructor simplification lemmas.
- Keep `target_runtime_typed_static_imp_assignable_context_mutual` and projections.
- Keep `assign_target_TopLevelVar_INL_imp_assignable_context`.
- Revise the generic INL bridge so it contains no cheat: either remove it if no theorem depends on it, or replace it with a proved base-target-only lemma.
- Use C5.4 static facts for INR statement branches where INL-success cannot be used.

#### Approach
The core bridge is two-step: prove static context for the evaluated assignment value, then use `target_runtime_typed_static_imp_assignable_context`. Successful assignment can still use `assign_target_TopLevelVar_INL_imp_assignable_context`, but failed/INR no-TypeError branches must use the repaired static target boundary from C5.4.

#### Not to try
Do not rely on the current cheated `assign_target_INL_imp_assignable_context_stmt_ind` TupleTargetV branch. If the theorem is unused, deleting it is preferable to proving a difficult sequential assignment lemma that no consumer needs.

### C5.2.1: Define static TopLevelVar context predicate for evaluated assignment values
- Kind: `definition`
- Risk: 1
- Rationale: This is a direct extraction of the TopLevelVar part of `assign_target_assignable_context_def`; it introduces no evaluator recursion and no semantic commitments beyond existing definitions.

#### Progress note
New helper definition introduced to replace the failed attempt to get TopLevelVar layout facts from `env_context_consistent`.

#### Summary
- Add `assignment_value_static_assignable_context cx gv` in the C5.2 block.
- It is `T` for non-TopLevel base locations.
- For `TopLevelVar`, it requires exactly the module/declaration/type-or-layout facts used by `assign_target_assignable_context_def`.
- For tuples, it recurses with `EVERY`.

#### Statement
Suggested definition:
```sml
Definition assignment_value_static_assignable_context_def:
  assignment_value_static_assignable_context cx (BaseTargetV loc sbs) =
    (case loc of
     | TopLevelVar src id =>
         ?code p. get_module_code cx src = SOME code /\
                  find_var_decl_by_num (string_to_num id) code = SOME p /\
                  (case FST p of
                   | StorageVarDecl is_transient typ =>
                       IS_SOME (evaluate_type (get_tenv cx) typ) /\
                       IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
                   | HashMapVarDecl is_transient kt vt =>
                       sbs <> [] /\
                       IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))))
     | _ => T) /\
  assignment_value_static_assignable_context cx (TupleTargetV tgts) =
    EVERY (assignment_value_static_assignable_context cx) tgts
End
```

#### Approach
This is definitional. Keep it near the existing bridge lemmas and do not give it a broad `[simp]` attribute until the constructor-specific rewrite lemmas in C5.2.2 are proved.

#### Not to try
Do not bake `env` or `env_context_consistent` into this predicate. The predicate describes concrete executable context/layout facts for an already evaluated assignment value, not static typing facts.

### C5.2.2: Constructor simplification lemmas for static context predicate
- Kind: `definition_probe`
- Risk: 1
- Rationale: These probes verify the new predicate computes in the exact shape needed by later proof branches and avoid repeatedly unfolding the whole definition in large statement goals.
- Dependencies: C5.2.1

#### Progress note
New computation probes for the replacement static-context interface.

#### Summary
- Prove `[simp]` lemmas for `ScopedVar` and `ImmutableVar` returning `T`.
- Prove a TopLevelVar expansion lemma matching the existential required by `assign_target_assignable_context_def`.
- Prove tuple expansion to `EVERY`.
- These lemmas are the intended public rewrite interface for the new predicate.

#### Statement
Suggested lemmas:
```sml
Theorem assignment_value_static_assignable_context_ScopedVar[simp]:
  assignment_value_static_assignable_context cx (BaseTargetV (ScopedVar id) sbs) = T

Theorem assignment_value_static_assignable_context_ImmutableVar[simp]:
  assignment_value_static_assignable_context cx (BaseTargetV (ImmutableVar id) sbs) = T

Theorem assignment_value_static_assignable_context_TupleTargetV[simp]:
  assignment_value_static_assignable_context cx (TupleTargetV gvs) =
  EVERY (assignment_value_static_assignable_context cx) gvs

Theorem assignment_value_static_assignable_context_TopLevelVar:
  assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) <=>
    ?code p. get_module_code cx src = SOME code /\
             find_var_decl_by_num (string_to_num id) code = SOME p /\
             (case FST p of
              | StorageVarDecl is_transient typ =>
                  IS_SOME (evaluate_type (get_tenv cx) typ) /\
                  IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
              | HashMapVarDecl is_transient kt vt =>
                  sbs <> [] /\
                  IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p)))
```

#### Approach
All proofs should be `simp[assignment_value_static_assignable_context_def]`, with the TopLevelVar theorem possibly requiring a one-line `Cases_on`/`rw` over `FST p` if simplification does not split the declaration form automatically.

#### Not to try
Do not unfold evaluator definitions here. These are pure predicate-computation probes.

### C5.2.3: Static-plus-runtime bridge to assign_target_assignable_context
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The proof follows the recursive definition of `assign_target_assignable_context`; the only substantive base case, ScopedVar, is already supported by prior C5.2 progress (`target_runtime_typed_ScopedVar_imp_assignable_context`).
- Dependencies: C5.2.1, C5.2.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0107, E0112

#### Progress note
Carries forward the proved/near-proved ScopedVar helper direction and packages it with the new static TopLevelVar predicate so statement INR branches have the right boundary lemma.

#### Summary
- Prove that `assignment_value_static_assignable_context` supplies the TopLevelVar part of `assign_target_assignable_context`.
- Use `target_runtime_typed` plus `env_consistent` for the ScopedVar dynamic assignability part.
- Handle `ImmutableVar` by simplification.
- Handle `TupleTargetV` pointwise using the tuple clauses of `target_runtime_typed_def` and `assign_target_assignable_context_def`.

#### Statement
Suggested theorem:
```sml
Theorem target_runtime_typed_static_imp_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv /\
    env_consistent env cx st /\
    assignment_value_static_assignable_context cx gv ==>
    assign_target_assignable_context cx gv st
```
If tuple recursion is awkward, prove the mutual/list form first:
```sml
Theorem target_runtime_typed_static_imp_assignable_context_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv /\ env_consistent env cx st /\
     assignment_value_static_assignable_context cx gv ==>
     assign_target_assignable_context cx gv st) /\
  (!env cx st tgts tys gvs.
     LIST_REL3 (target_runtime_typed env cx st) tgts tys gvs /\
     env_consistent env cx st /\
     EVERY (assignment_value_static_assignable_context cx) gvs ==>
     EVERY (assign_target_assignable_context cx) gvs)
```

#### Approach
Start with case analysis on `gv`; for base targets, split `loc`. In the ScopedVar branch, use the existing local/helper theorem `target_runtime_typed_ScopedVar_imp_assignable_context` or recreate its proof from `target_runtime_typed_ScopedVar_imp_var_assignable`, `env_scopes_consistent_var_assignable_imp`, and `lookup_scopes_find_containing_scope`. In the tuple branch, unfold `target_runtime_typed_def` just enough to get `target_values_runtime_typed`, then induct over `gvs`/`tgts`/`tys` or use the mutual statement.

#### Not to try
Do not unfold `assign_target_def`. Do not attempt to prove TopLevelVar code/layout facts from `target_runtime_typed`; for TopLevelVar, `location_runtime_typed_def` only gives `FLOOKUP env.toplevel_vtypes`.

### C5.2.4: Prove TopLevelVar INL-success implies assignable context
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: For an INL result, every missing TopLevelVar context component would have caused a preceding `lift_option_type`, `type_check`, or bind to return `INR`; controlled case splitting suffices.
- Dependencies: C5.2.2
- Progress transition: `refinement`
- Carries progress/evidence from: E0108, E0109, E0111

#### Progress note
Continues the earlier success-bridge work but avoids the previous uncontrolled `assign_target_def` expansion by proving small sequencing facts per branch.

#### Summary
- Replace the cheat in `assign_target_TopLevelVar_INL_imp_assignable_context`.
- First derive `lookup_global cx src (string_to_num id) st = (INL tv, r)` from the successful `assign_target` call.
- Then split on `tv`: `Value`, `HashMapRef`, `ArrayRef`.
- In each branch, recover the declaration/layout/evaluate-type facts from the monadic steps needed before `INL` can be returned.

#### Statement
Existing theorem to prove in place:
```sml
Theorem assign_target_TopLevelVar_INL_imp_assignable_context:
  !cx src id sbs op st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') ==>
    assign_target_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) st
```
Useful strict helpers may be added locally if needed, for example:
```sml
Theorem assign_target_TopLevelVar_INL_imp_static_context:
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') ==>
  assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs)
```

#### Approach
Use the already present `assign_target_TopLevelVar_success_imp_lookup_global_INL` to expose the initial lookup. Then open `assign_target_def` only under the fixed `BaseTargetV (TopLevelVar src id) sbs` pattern and case split the result of `lookup_global`, `get_module_code`, `find_var_decl_by_num`, `lookup_var_slot_from_layout`, `evaluate_type`, and the `tv` constructor as needed. Close `IS_SOME` goals by preserving witnesses from successful `SOME` case splits, not by `metis_tac[IS_SOME_EXISTS]`.

#### Not to try
Do not unfold all clauses of `assign_target_def` globally. Do not use `no_type_error_result`; INL success is stronger and should be used directly. Do not let `simp[AllCaseEqs()]` erase witnesses needed for `IS_SOME` goals.

### C5.2.5: Remove or prove the unused generic INL assignable-context bridge
- Kind: `cheat_elimination`
- Risk: 1
- Rationale: Dossier E0122 records that the theorem with the TupleTargetV cheat has zero downstream consumers. Eliminating an unused local/exported helper or replacing it with a base-target-only proved theorem is mechanical and required for zero CHEAT warnings.
- Progress transition: `refinement`
- Carries progress/evidence from: E0122

#### Progress note
This revises the old not-started C5.2.5: it is no longer optional because the source contains a `cheat` in this helper block.

#### Summary
The theorem `assign_target_INL_imp_assignable_context_stmt_ind` currently has a cheated TupleTargetV branch. Before proceeding, grep for consumers of both it and `assign_target_INL_imp_assignable_context_stmt`. If there are no consumers, delete both the local theorem and wrapper. If a consumer exists, replace them by a proved base-target-only lemma sufficient for that consumer.

#### Statement
Preferred deletion path: remove these theorems if unused:
```sml
assign_target_INL_imp_assignable_context_stmt_ind
assign_target_INL_imp_assignable_context_stmt
```
Fallback proved replacement if a consumer exists:
```sml
Theorem assign_base_target_INL_imp_assignable_context_stmt:
  !cx loc sbs op st res st' bt env ty st_pre st_pre'.
    assign_target cx (BaseTargetV loc sbs) op st = (INL res, st') /\
    eval_base_target cx bt st_pre = (INL (loc,sbs), st_pre') /\
    well_typed_target env bt ty /\
    env_consistent env cx st ==>
    assign_target_assignable_context cx (BaseTargetV loc sbs) st
```

#### Approach
Start with a grep for theorem names in `semantics/prop`. If unused, delete; HOL theories do not need unused helper theorems. If a consumer exists, prove only the BaseTargetV version by cases on `loc`: ScopedVar uses `eval_target_assignable`/existing scoped bridge, ImmutableVar simplifies, TopLevelVar uses `assign_target_TopLevelVar_INL_imp_assignable_context`.

#### Not to try
Do not attempt the full TupleTargetV theorem by induction over `assign_targets` unless a real consumer requires it. Sequential tuple assignment changes state between components, so proving every component assignable in the original state is not the cheap path.

### C5.2.6: Shape side-condition boundary for Replace assignments
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: Prior evidence from E0113 says the shape side condition is already derivable using `assign_operation_matches_target_shape_Replace_from_typed`; this component records the exact reusable boundary lemma so statement cases avoid ad hoc BaseTarget-only reasoning.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0113

#### Progress note
Carries forward the successful E0113 attempt showing that `assign_operation_matches_target_shape_Replace_from_typed` works for both `BaseTargetV` and `TupleTargetV`.

#### Summary
- Add/use a small wrapper lemma for `Replace` operations if current call sites still try `assign_operation_matches_target_shape_BaseTargetV`.
- The lemma should work uniformly for base and tuple targets.
- It consumes `target_runtime_typed`, `evaluate_type`, and `value_has_type`, all already available in AnnAssign/Assign successful value branches.

#### Statement
Suggested wrapper, if not already convenient enough to use directly:
```sml
Theorem assign_operation_matches_target_shape_Replace_stmt:
  !env cx st tgt ty gv tv v.
    target_runtime_typed env cx st tgt ty gv /\
    evaluate_type env.type_defs ty = SOME tv /\
    value_has_type tv v ==>
    assign_operation_matches_target_shape gv (Replace v)
```
Proof should be by `metis_tac[assign_operation_matches_target_shape_Replace_from_typed]`.

#### Approach
Use the existing theorem directly; only add this wrapper if it improves matching in statement proofs. This avoids the known failure mode where `assign_operation_matches_target_shape_BaseTargetV` is applied to a possibly tuple-valued target.

#### Not to try
Do not case split on `gv` in statement assignment branches merely to prove shape. The existing typedness theorem already captures the tuple length argument.

### C5.2.7: C5.2 integration checkpoint for statement INR branches
- Kind: `checkpoint`
- Risk: 1
- Rationale: This is a proof-interface audit, not a mathematical unknown: after C5.2.3-C5.2.6, any remaining failure must be due to the statement theorem lacking a static writable-target premise, not due to the boundary lemmas.
- Dependencies: C5.2.3, C5.2.5, C5.2.6
- Checkpoint: yes
- Carries progress/evidence from: E0113

#### Progress note
Records the strategic consequence of E0113: if no static context premise is present, C5.2 cannot honestly manufacture TopLevelVar layout facts.

#### Summary
- Build `vyperTypeStmtSoundnessTheory` far enough to confirm the two C5.2 cheats are gone.
- At any Assign/AnnAssign/AugAssign call to `assign_target_no_type_error`, use C5.2.6 for shape.
- For INL-success branches, use C5.2.5.
- For INR/no-TypeError branches, use C5.2.3 only if a static `assignment_value_static_assignable_context` fact is available.
- If such a fact is absent, stop and escalate for broader C5/type-statement invariant redesign.

#### Statement
No new HOL theorem is required for this checkpoint. The executable criterion is: the C5.2 local lemmas compile without cheats, and no proof step tries to derive TopLevelVar `get_module_code`/layout facts from `env_context_consistent` alone.

#### Approach
After proving the boundary lemmas, inspect the stuck statement branch. If the branch has `assign_target ... = (INL _, _)`, use C5.2.5. If it has `assign_target ... = (INR _, _)`, require an explicit `assignment_value_static_assignable_context cx gv` fact and then use C5.2.3; otherwise escalate for a broader statement-typing/static-assignability invariant.

#### Not to try
Do not add a local cheat or an axiom-like lemma saying `env_context_consistent` supplies TopLevelVar writability. Do not silently strengthen public wrapper statements inside C5.2; that is outside this subtree.

### C5.3: AnnAssign assignable-type consequences
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: Already discharged by existing lemmas `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV`.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0123

#### Progress note
No further C5 work needed for AnnAssign NoneT/NoneTV side conditions.

#### Summary
Carry forward the completed AnnAssign helper path. AnnAssign uses `assignable_type` to rule out `NoneT`, then transfers that to non-`NoneTV` after `evaluate_type`. Existing source already uses the relevant lemmas in the AnnAssign resume proof.

#### Statement
Existing lemmas suffice:
```sml
assignable_type_not_NoneT
evaluate_type_not_NoneT_imp_not_NoneTV
assignable_type_evaluate_not_NoneTV
```

#### Approach
No new proof required unless later edits break imports. If a statement branch asks for non-None runtime type, solve by `metis_tac`/`simp` with the three listed lemmas.

#### Not to try
Do not introduce a second AnnAssign-specific non-None predicate; the existing `assignable_type` interface is enough.

### C5.4: Top-level assignment static-writability repair and tuple/list packaging
- Kind: `definition_and_boundary_repair`
- Risk: 2
- Rationale: E0124 pinpointed the missing invariant. The repair is narrow: reject immutable top-level assignment targets statically and strengthen env-context consistency for remaining top-level target entries. The downstream packaging then follows by existing runtime/static bridge lemmas and list reasoning.
- Dependencies: C5.2.5
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0124
- Invalidates prior progress/evidence: old C5.4 tuple/list-only plan

#### Progress note
The old C5.4 treated tuple/list packaging as the main problem, but E0124 showed the real blocker is the static TopLevelVar context gap. This replacement keeps tuple/list packaging as a child but makes the static-writability repair the prerequisite.

#### Summary
- Modify assignment target typing so `TopLevelNameTarget` does not typecheck as an assignment target when it denotes a bare-global/immutable entry.
- Strengthen `env_context_consistent_def` so non-immutable top-level `Type` entries have storage declaration/evaluate_type/layout-slot facts, and `HashMapT` entries have hashmap declaration/layout-slot facts.
- Prove projection lemmas from the strengthened context; statement proofs should consume projections, not unfold the whole context repeatedly.
- Prove that evaluated well-typed top-level targets have `assignment_value_static_assignable_context`.
- Use `EVERY`/`LIST_REL3` packaging for tuple/list assignment values.

#### Description
This component may edit `vyperTypeSystemScript.sml` as a strict prerequisite for C5. Keep the changes minimal and source-compatible for expression typing: reading top-level names remains governed by `well_typed_expr`/`type_place_expr`; only assignment-target typing is restricted.

#### Approach
Make the static definition repair first, then restore build by updating any simplification proofs broken by the extra conjuncts. After that, prove small projection lemmas and use them to derive `assignment_value_static_assignable_context` for TopLevelVar cases.

#### Not to try
Do not add `functions_well_typed cx` to `assign_target_assignable_context`; this predicate is intentionally about a concrete target/state/context and should stay independent of global function-body typing. Do not encode cx-dependent code/layout checks inside `type_place_target`, because that definition only receives `env`.

#### Argument
A top-level assignment target can only be no-TypeError if the evaluator's `TopLevelVar` branch has the static code/declaration/layout facts that `assign_target_def` checks before performing the update. The old invariant only said every `toplevel_vtypes` entry is well formed, and only related entries to code under an already-assumed `get_module_code`; this cannot establish the existential demanded by `assign_target_assignable_context`.

The correct invariant is attached to assignable top-level target entries. Static assignment target typing rejects bare-global/immutable entries using `env.bare_globals`; for the remaining entries, env/context consistency provides the storage/hashmap declaration and layout facts. Runtime target typing supplies the actual `FLOOKUP env.toplevel_vtypes` root vtype and target-path typing supplies subscript information. Therefore storage roots satisfy the StorageVarDecl case of `assignment_value_static_assignable_context`, and hashmap roots satisfy the HashMapVarDecl case with `sbs <> []` because typed assignment to a value below a hashmap must consume at least one subscript.

For tuple targets, `target_values_runtime_typed` and `target_values_shape` align the static and runtime lists. The proof should map the single-target static-context lemma over the list and feed the result to `target_values_runtime_typed_static_imp_EVERY_assignable_context`.

#### Definition design
Definition change interface:
1. `type_place_target env (TopLevelNameTarget (src,id))` must return `NONE` when `FLOOKUP env.bare_globals (src,string_to_num id) = SOME _`; otherwise it may return the existing `FLOOKUP env.toplevel_vtypes` result.
2. `env_context_consistent_def` must include projection-friendly clauses for non-bare-global `Type ty` top-level entries and for `HashMapT kt vt` top-level entries. These clauses must conclude existence of `get_module_code`, `find_var_decl_by_num`, and `lookup_var_slot_from_layout` facts matching `assignment_value_static_assignable_context_TopLevelVar`.
3. Add named projection lemmas immediately after the definitions or in the nearest env helper file.

Failure signs: if `TopLevelNameTarget` for an immutable/bare-global entry remains well-typed as a target, stop and escalate; if projection lemmas still require an external `get_module_code` hypothesis, the env-context strengthening is insufficient.

#### Code structure
Put definition edits in `vyperTypeSystemScript.sml` at `type_place_target` and `env_context_consistent_def`. Put simple projection lemmas either directly after `env_context_consistent_def` if the file already has theorem blocks there, or in the first imported prop helper file that can see `env_context_consistent_def`. Put C5 consumer lemmas in `vyperTypeStmtSoundnessScript.sml` in the existing C5 helper block, after `assignment_value_static_assignable_context_TopLevelVar` and before statement resumes.

### C5.4.1: Repair TopLevelNameTarget target typing and env_context_consistent static clauses
- Kind: `definition`
- Risk: 2
- Rationale: The definition changes are narrow and directly match the missing facts from E0124. Some existing simp proofs will need routine updates for the new env_context_consistent conjuncts, but no evaluator recursion is involved.
- Dependencies: C5.2.5
- Checkpoint: yes
- Carries progress/evidence from: E0124

#### Progress note
This is the executable repair for the E0124 architectural gap.

#### Summary
Change `type_place_target` for `TopLevelNameTarget` to reject bare-global/immutable entries. Strengthen `env_context_consistent_def` with existence clauses for writable top-level storage and hashmap entries. Rebuild the immediate theories and repair only proofs broken by the extra conjuncts/simplification.

#### Statement
Definition shape to implement:
```sml
(* in type_place_target clauses *)
type_place_target env (TopLevelNameTarget (src_id_opt, id)) =
  (let n = string_to_num id in
   if IS_SOME (FLOOKUP env.bare_globals (src_id_opt,n)) then NONE
   else FLOOKUP env.toplevel_vtypes (src_id_opt,n))
```
Strengthen `env_context_consistent_def` with clauses equivalent to:
```sml
(!src id ty.
   FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
   FLOOKUP env.bare_globals (src,id) = NONE ==>
   ?ts is_transient typ id_str.
     get_module_code cx src = SOME ts /\
     find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
     typ = ty /\
     IS_SOME (evaluate_type (get_tenv cx) typ) /\
     IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str))
```
and strengthen/replace the existing HashMapT clause so it concludes, without an input `get_module_code` hypothesis:
```sml
(!src id kt vt.
   FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
   ?ts is_transient id_str.
     get_module_code cx src = SOME ts /\
     find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
     IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str))
```

#### Approach
Edit definitions first, then update simple lemmas that unfold `env_context_consistent_def` by adding the new conjunct goals; most should close by carrying assumptions through env-extension records or by `metis_tac` from the old context assumption. For `type_place_target_TopLevelNameTarget` and any direct simplification theorem, update the statement to include the `bare_globals` rejection condition.

#### Not to try
Do not remove the existing bare-global clause from `env_context_consistent_def`; expression/immutable reasoning still uses it. Do not require storage declarations for all `Type` top-level entries including bare globals, because that would make ordinary immutable environments inconsistent.

### C5.4.2: Projection lemmas for writable top-level context entries
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: Once C5.4.1 changes the definition, these are direct unfold/projection lemmas. They prevent statement proofs from depending on the full shape of `env_context_consistent_def`.
- Dependencies: C5.4.1

#### Progress note
New helper interface produced by the C5.4 repair.

#### Summary
Add named lemmas extracting storage and hashmap static facts from `env_consistent`/`env_context_consistent`. These lemmas should conclude exactly the existential facts needed by `assignment_value_static_assignable_context_TopLevelVar`. Use them in all later C5.4 proofs.

#### Statement
Suggested lemmas:
```sml
Theorem env_consistent_toplevel_storage_static:
  env_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
  FLOOKUP env.bare_globals (src,id) = NONE ==>
  ?ts is_transient id_str.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient ty,id_str) /\
    IS_SOME (evaluate_type (get_tenv cx) ty) /\
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)

Theorem env_consistent_toplevel_hashmap_static:
  env_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
  ?ts is_transient id_str.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
```

#### Approach
Unfold `env_consistent_def` and `env_context_consistent_def`, then instantiate the new conjuncts. Keep the conclusions in the same constructor/order as `assignment_value_static_assignable_context_TopLevelVar` to make later `metis_tac` work.

#### Not to try
Do not state these lemmas with an extra `get_module_code cx src = SOME ts` hypothesis; the whole point is to get that fact from consistency.

### C5.4.3: Static assignable context for evaluated TopLevelVar targets
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: This is a structural proof over target path typing plus a case split on the root top-level vtype. The only nontrivial fact is hashmap non-emptiness, which follows from `target_path_type` starting at `HashMapT`.
- Dependencies: C5.4.2
- Carries progress/evidence from: E0116

#### Progress note
This produces the missing premise for C5.2.3 in INR statement branches.

#### Summary
Prove that a well-typed, runtime-typed evaluated target value has `assignment_value_static_assignable_context`, including TopLevelVar. Storage roots use the storage projection lemma. Hashmap roots use the hashmap projection lemma plus a small path lemma showing the subscript list is nonempty. Tuple roots map the theorem over components.

#### Statement
Helpful path lemma:
```sml
Theorem target_path_type_HashMapT_imp_sbs_ne:
  target_path_type env (HashMapT kt vt) sbs (Type ty) ==> sbs <> []
```
Main mutual bridge:
```sml
Theorem target_runtime_typed_imp_static_assignable_context_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv /\
     env_consistent env cx st ==>
     assignment_value_static_assignable_context cx gv) /\
  (!env cx st tgts tys gvs.
     target_values_runtime_typed env cx st tgts tys gvs /\
     env_consistent env cx st ==>
     EVERY (assignment_value_static_assignable_context cx) gvs)
```

#### Approach
Use the induction principle for `target_runtime_typed`/`target_values_runtime_typed` if available; otherwise prove by cases on the target/value shapes and list induction for the values relation. In the BaseTargetV TopLevelVar branch, unfold `location_runtime_typed_def` to get the root `FLOOKUP`; then cases on the root vtype. Storage uses `env_consistent_toplevel_storage_static`; HashMap uses `env_consistent_toplevel_hashmap_static` and `target_path_type_HashMapT_imp_sbs_ne`.

#### Not to try
Do not expand `assign_target_def` here. This lemma is about static context of an already evaluated target, not about executing the assignment.

### C5.4.4: Full assignable-context packaging for statement assignment targets
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: After C5.4.3 and the carried-forward C5.2.3 bridge, full assignable context is a direct composition. Tuple/list packaging is exactly the list projection of the mutual lemmas.
- Dependencies: C5.4.3, C5.2
- Carries progress/evidence from: E0116, E0124

#### Progress note
This replaces the old blocked tuple/list packaging goal with a composition of static-context and runtime-context bridges.

#### Summary
Compose static assignability with runtime typedness to produce `assign_target_assignable_context` and its `EVERY` list form. These are the theorems statement assignment branches should call in INR/no-TypeError subcases. No evaluator unfolding should remain at call sites.

#### Statement
```sml
Theorem target_runtime_typed_imp_assignable_context:
  target_runtime_typed env cx st tgt ty gv /\
  env_consistent env cx st ==>
  assign_target_assignable_context cx gv st

Theorem target_values_runtime_typed_imp_EVERY_assignable_context:
  target_values_runtime_typed env cx st tgts tys gvs /\
  env_consistent env cx st ==>
  EVERY (\gv. assign_target_assignable_context cx gv st) gvs
```

#### Approach
For the single-target theorem, apply C5.4.3 to get `assignment_value_static_assignable_context`, then apply `target_runtime_typed_static_imp_assignable_context`. For the list theorem, use the list conjuncts of both mutual lemmas and `target_values_runtime_typed_static_imp_EVERY_assignable_context`.

#### Not to try
Do not duplicate the ScopedVar/TopLevelVar/TupleTargetV case split here; that belongs in C5.4.3 and the existing C5.2 bridge.

### C5.4.5: Patch Assign/AugAssign C5 side-condition call sites only
- Kind: `integration`
- Risk: 2
- Rationale: With shape and assignable-context bridges available, the remaining C5-owned statement holes are local proof wiring in the assignment resumes. Broader builtin/update-binop obligations remain outside C5 unless they block these side-condition calls.
- Dependencies: C5.1, C5.3, C5.4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0117, E0118, E0122

#### Progress note
This component authorizes only the side-condition repairs in assignment statement branches, not unrelated statement cheats.

#### Summary
Use the new full-context lemmas in `eval_all_type_sound_mutual[Assign]` INR/no-TypeError subcases. Use the existing shape lemma for Replace. In AugAssign, derive the BaseTargetV runtime target and use the same context bridge for update assignment; leave non-C5 builtin/update-binop blockers to their own components if encountered.

#### Statement
No new public theorem. The target is to replace C5-side-condition cheats in:
```sml
Resume eval_all_type_sound_mutual[Assign]
Resume eval_all_type_sound_mutual[AugAssign]
```
where the missing facts are:
```sml
assign_operation_matches_target_shape gv op
assign_target_assignable_context cx gv st
```

#### Approach
In Assign, after rebuilding `target_runtime_typed env cx st2 tgt (expr_type e) gv`, call `target_runtime_typed_imp_assignable_context` at the state used by `assign_target`, using env consistency preserved through expression/materialise steps. For Replace shape, call `assign_operation_matches_target_shape_Replace_from_typed`. In AugAssign, first rebuild the BaseTarget target runtime fact from the base-target IH, then use the same context bridge; update-binop no-TypeError lemmas may still be external blockers and should be escalated if they are not C5 side-condition issues.

#### Not to try
Do not solve AugAssign by expanding all of `well_typed_binop` or builtin arithmetic here. C5 only owns deriving assignment shape/context side conditions; inherited update-binop no-TypeError obligations are separate unless the proof goal is exactly one of these side conditions.

### C6: Assignment cases of `eval_all_type_sound_mutual`
- Kind: `mutual_theorem_cases`
- Risk: 2
- Rationale: After C5, assignment branches are integration: expression/target evaluation gives typed runtime inputs, bridge lemmas derive C3 side conditions, and C3/C4 provides assignment soundness.
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
- Include statement-list, loop/iterator, target, expression, and expression-list branches only if C0 shows they are current/reachable.
- Use existing env-extension, env-preservation, scope-pop, builtin, and assignment interfaces.
- Strengthen the existing joint invariant if a downstream property is missing; do not fork a parallel proof.

#### Statement
Complete all current-source unfinished branches inside `semantics/prop/vyperTypeStmtSoundnessScript.sml` evaluator mutual theorem(s) reachable from `vyperSemanticsHolTheory` and not assignment branches covered by C6.

#### Approach
For each branch, consume the layer theorem matching the evaluator call: expression/target soundness for expression/target branches, scope-pop and env preservation for scoped blocks/loops, C1 builtin soundness for builtin expressions, and C6 assignment soundness for assignment statements. Preserve the all-result invariant through the evaluator’s real recursive calls.

#### Not to try
Do not create standalone `*_no_type_error` induction trees over the same evaluator. Do not prove call-entry setup here if the branch belongs in C8.

### C8: Call and callable-body soundness wrappers
- Kind: `corollary_cluster`
- Risk: 2
- Rationale: The TASK lists call wrappers as reachable obligations. After statement soundness, these should be call-entry setup plus projections, not a new evaluator induction.
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
Keep the public file as a projection layer from completed joint theorems. If internal statements were strengthened or renamed, add compatibility corollaries of equivalent public strength and update imports. Finish with a reachable-cheat audit tied back to C0.

#### Not to try
Do not weaken the frozen public behavior. Do not claim completion from a successful build if HOL reports reachable CHEAT warnings.
