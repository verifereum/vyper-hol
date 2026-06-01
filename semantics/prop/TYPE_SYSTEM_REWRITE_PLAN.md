# Vyper Type System Rewrite Plan

Goal: replace the current messy `vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, and `vyperTypeSoundness` development with a fresh, executable type system and clean soundness proof stack.

## Requirements

The new development should provide:

1. **Executable type checking** — statement/program typing should be computable by `EVAL`.
2. **No-TypeError soundness** — well-typed evaluation never returns `INR (Error (TypeError s))`.
3. **Result correctness / preservation** — expression results, materialised values, returns, state, env consistency, and accounts remain well-typed.

## Strategy

Do not mutate the old proof stack in place. Build new theories with new names, then switch over and delete/retire the old theories once complete.

### Core proof principle: prove the strongest joint invariant

**Always prove the strongest joint invariant that follows the evaluator/recursive
structure.**  Do not split no-TypeError, result typing, state preservation,
environment preservation, accounts preservation, assignability preservation, and
exception/return typing into separate parallel proof trees when they use the same
case split or induction.

The workhorse theorem for an evaluator should have one combined postcondition,
for example:

```sml
state_well_typed st' /\
accounts_well_typed st'.accounts /\
env_consistent ... st' /\
no_type_error_result res /\
case res of
| INL v => result_runtime_typed ... v
| INR exn => exception_or_error_typed ... exn
```

Then derive small public wrapper theorems such as `*_no_type_error` or
`*_success_preserves_state` as corollaries.  These wrappers are for the external
API only; they should not drive the internal proof architecture.

Rationale:

- no-TypeError and preservation usually require the same semantic facts;
- separated helpers duplicate evaluator case analysis;
- separated helpers often fail because they lack the strengthened induction
  hypotheses already available in the mutual theorem;
- if a property is needed later, strengthen the existing mutual/frame invariant
  rather than starting a second induction over the same evaluator.

Concrete example: assignment no-TypeError should not be proved by independent
lemmas such as `assign_target_append_no_type_error` that reconstruct target
runtime typing from scratch.  The preferred shape is a joint assignment theorem
from `target_runtime_typed` and `assign_operation_runtime_typed` that proves both
no-TypeError and state/env/accounts preservation.  The legacy no-TypeError
lemmas should become one-line compatibility corollaries or disappear from the
internal proof path.

Current fresh theory stack:

- `vyperTypeSystemScript.sml` — new executable type-system definitions.
- `vyperTypeValuesScript.sml` — pure value/type lemmas.
- `vyperTypeEnvScript.sml` — env/state/scope/immutable consistency lemmas.
- `vyperTypeEnvExtensionScript.sml` — static typing-env extension/weakening layer.
- `vyperTypeEnvPreservationScript.sml` — frame-style env consistency preservation lemmas.
- `vyperTypeScopePopScript.sml` — pushed-scope execution/pop restoration layer.
- `vyperTypeBytesCryptoScript.sml` — bytes/crypto value typing helpers.
- `vyperTypeDefaultsScript.sml` — default argument typing helpers.
- `vyperTypeConversionsScript.sml` — conversion typing helpers.
- `vyperTypeABIScript.sml` — ABI typing helpers.
- `vyperTypeBuiltinsScript.sml` — clean replacement for builtin/type-builtin/binop facts.
- `vyperTypeExprSoundnessScript.sml` — expression/iterator/target no-TypeError and preservation theorem layer.
- `vyperTypeStatePreservationScript.sml` — state-update, scope, materialisation, assignment preservation lemmas.
- `vyperTypeAssignSoundnessScript.sml` — assignment-target error-shape, context, and no-TypeError helpers.
- `vyperTypeStmtSoundnessScript.sml` — statement/statement-list no-TypeError and preservation theorem layer.
- `vyperTypeCallSoundnessScript.sml` — call-entry and internal/external/special call theorem layer.
- `vyperTypeSoundnessNewScript.sml` — final public theorem surface.

The aggregator `vyperSemanticsHolScript.sml` has been switched to import `vyperTypeSoundnessNew` rather than the old final theory.

## Assignment target soundness progress update (2026-05-29)

This section records the current state of the focused assignment-target no-TypeError work in
`semantics/prop/vyperTypeStatePreservationScript.sml`, especially the `TopLevelVar` case of
`assign_target_sound_mutual`.

### Proof engineering discipline learned / required

For this proof, broad cleanup after case explosion is not workable. In particular:

- Do **not** use a large `gvs[..., AllCaseEqs(), ...]` and then try to clean up many parallel goals.
- Split semantic cases at the point where the evaluator branches, and close each branch immediately.
- Before using fragile tactics (`drule_all`, `metis_tac`, broad `gvs`, etc.), make sure the proof is in a single active branch.
- Prefer branch helper lemmas that exactly match semantic branches.
- When asking for/providing the mathematical proof of a branch, give the exact sequence of lemmas to use and the subgoals to establish; avoid extra prose.

The successful pattern used for storage `Value` branches is:

```sml
strip_tac >>
drule_all some_exact_helper >> strip_tac >>
...
qhdtm_x_assum `set_global` mp_tac >> simp[] >>
irule exact_no_type_error_theorem >>
goal_assum drule_all
```

and, inside `sound_TopLevelVar`, eliminate impossible subcases early with exact lemmas such as
`lookup_global_Value_not_HashMapVarDecl` before destructing further.

### Strengthened invariants / definitions now in place

- `target_path_step_type` for `HashMapT kt vt` now requires `ValueSubscript key`, `hashmap_key_type kt`, successful evaluation of the key type, and `value_has_type` for the key value.
- `assign_operation_runtime_typed` was strengthened for `PopOp`: it now requires a dynamic array type.
- `assignable_type` was added to `vyperTypeSystemScript.sml` and used in assignment/materialized-value statement typing rules. It excludes `NoneT` recursively through tuples/arrays/structs.
- `assign_target_assignable_context` was added for runtime assignment validity, especially top-level writability. For `TopLevelVar`, it requires module code, a declaration, and layout-slot success; storage declarations require type evaluation, hashmap declarations require nonempty subscripts and slot success.

### Important proved helper lemmas

Non-None / assignability:

```sml
assignable_type_not_NoneT
evaluate_type_not_NoneT_imp_not_NoneTV
assignable_type_evaluate_not_NoneTV
```

Recursive assignment no-TypeError and preservation support (all proved, no inherited cheats):

```sml
assign_subscripts_no_type_error_from_leaf
assign_operation_runtime_typed_leaf_no_type_error
assign_subscripts_no_type_error_runtime_typed
assign_subscripts_preserves_type_runtime_typed
```

The update-binop chain that was previously cheated is now fully proved:

```sml
well_typed_binop_no_type_error                         (* proved, in vyperTypeBuiltinsScript.sml *)
well_typed_update_binop_no_type_error                  (* derived from above via metis_tac *)
assign_subscripts_update_leaf_no_type_error            (* derived via well_typed_update_binop_no_type_error *)
```

Storage/top-level helpers:

```sml
lookup_global_success_get_module_code
top_level_Type_storage_decl
top_level_Type_not_hashmap_decl
top_level_HashMap_decl
top_level_vtype_well_formed
target_runtime_typed_top_level_Type
lookup_global_Value_not_HashMapVarDecl
lookup_global_top_level_assignable_no_type_error
lookup_global_storage_Value_typed
write_storage_slot_no_type_error_from_value_has_type
set_global_storage_no_type_error
top_level_vtype_Type_storage_decl
top_level_storage_value_leaf_evaluate_type
top_level_storage_value_assign_success_no_type_error
top_level_storage_value_assign_subscripts_no_type_error
```

Top-level HashMapRef / ArrayRef helpers (proved for the completed TopLevelVar branches):

```sml
assign_target_HashMapRef_branch_no_type_error
lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef
assign_target_TopLevelVar_ArrayRef_branch_no_type_error
assign_target_TopLevelVar_ArrayRef_AppendOp_dynamic_no_type_error
assign_target_TopLevelVar_ArrayRef_PopOp_dynamic_no_type_error
assign_target_TopLevelVar_ArrayRef_resolve_error_no_type_error
top_level_HashMapRef_assign_no_type_error
lookup_global_HashMapRef
```

Notes:

- `lookup_global_top_level_assignable_no_type_error` rules out a TypeError result from `lookup_global` using only `assign_target_assignable_context`; this works because `read_storage_slot_error` says storage read errors are `RuntimeError`, not `TypeError`.
- `top_level_storage_value_leaf_evaluate_type` is the key bridge from top-level target typing to the executable storage root type:

```sml
evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))
```

- `top_level_storage_value_assign_success_no_type_error` closes the storage `Value` branch where `assign_subscripts` succeeds but `set_global` allegedly returns a TypeError.
- `top_level_storage_value_assign_subscripts_no_type_error` closes the storage `Value` branch where `assign_subscripts` allegedly returns `INR (TypeError msg)`.

### Current status of `assign_target_sound_mutual`

**All branches of `assign_target_sound_mutual` are proved with no cheats.**

This includes:

```sml
assign_target_sound_mutual[sound_ScopedVar]      (* proved *)
assign_target_sound_mutual[sound_TopLevelVar]     (* proved, including Type/Value, Type/ArrayRef,
                                                      HashMapT/HashMapRef cases *)
assign_target_sound_mutual[sound_ImmutableVar]     (* proved *)
assign_target_sound_mutual[sound_TupleTargetV]     (* proved *)
assign_target_sound_mutual[sound_assign_targets_cons] (* proved *)
```

The `sound_TopLevelVar` proof dispatches by `vt` (Type vs HashMapT):

- **`Type t` case:** Uses `assign_target_assignable_context` to derive declaration facts.
  Dispatches by `root_tv` after `evaluate_type`:
  - Non-`ArrayTV` roots (BaseTV, TupleTV, StructTV, FlagTV, NoneTV): closed by
    `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`.
  - `ArrayTV` root: derives `ArrayRef` via
    `lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef`, then closed by
    `assign_target_TopLevelVar_ArrayRef_branch_no_type_error` (which handles
    `AppendOp`/`PopOp`/resolve/assignment subcases).
  - `HashMapVarDecl` sub-elimination via `top_level_Type_not_hashmap_decl`.

- **`HashMapT kt vt` case:** Uses `assign_target_assignable_context` to derive declaration facts.
  - `StorageVarDecl` sub-elimination via `top_level_HashMapT_not_storage_decl`.
  - `HashMapVarDecl`: derives slot and well-formedness, then closed by
    `top_level_HashMapRef_assign_no_type_error` (which delegates to
    `assign_target_HashMapRef_branch_no_type_error`).

### Statement assignment branches

The previously cheated assignment statement branches are now all proved:

```sml
eval_all_type_sound_mutual[AnnAssign]    (* proved *)
eval_all_type_sound_mutual[Assign]       (* proved *)
eval_all_type_sound_mutual[AugAssign]    (* proved *)
```

The strengthened runtime assignment side conditions are derived in each branch:

1. `assign_operation_matches_target_shape` — derived from typing/evaluation facts.
2. `assign_target_assignable_context` — derived from `target_runtime_typed_imp_assignable_context` or direct construction.
3. `assignable_type` used to derive non-`NoneT` side conditions for `AnnAssign`.
4. Tuple/list assignment uses `target_assignment_values_assignable` and rebuild lemmas.


## Current status (2026-05-31)

### ExtCall unblocking update (2026-06-01)

The fresh type-system rewrite is currently focused on
`eval_all_type_sound_mutual[Expr_Call_ExtCall]`.  Earlier attempts showed a real
proof-interface problem when trying to recover the optional-driver recursive IH
from the top-level Resume context.  Maintainer clarification now authorizes a
bounded proof-only probe inside `semantics/prop`: keep the semantics/evaluator
unchanged, but refactor the proof architecture and step through the ExtCall
monadic chain linearly.

The former stop gate is therefore narrowed, not discarded.  Do not try to derive
a compact driver premise from the unsplit top-level generated prefix.  It is now
acceptable to specialize the generated optional-driver IH **only after** the
proof has reached a single concrete ExtCall success-continuation branch where the
argument evaluation, checks/lifts, calldata construction, external call, and
account/transient updates have already been split/discharged.

Evidence from the C1.2 checkpoint:

- The proposed compact bridge
  `extcall_driver_continuation_premise_from_compact_ih` was tautological: it
  consumed exactly the desired compact optional-driver premise and did not derive
  that premise from the live mutual proof context.
- The live `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]` context exposes
  the optional-driver recursive IH only under the full generated ExtCall monadic
  prefix, including `eval_exprs`, `check`, `lift_option`,
  `build_ext_calldata`, `run_ext_call`, `update_accounts`, and
  `update_transient` temporaries.
- No compact standalone premise of the shape consumed by
  `extcall_success_continuation_sound_cond_driver_ih` is naturally available in
  the Resume context.
- Recovering that premise locally would require the already-ruled-out brittle
  generated-prefix specialization/simplification path.

Authorized proof-only path before continuing:

- Keep edits under `semantics/prop` and do not change evaluator/semantics
  definitions.
- Refactor proof architecture as needed inside the fresh proof stack.
- Prove the ExtCall branch linearly: close the place-expression half first,
  unfold typing/evaluation once, split `eval_exprs`, checks/lifts,
  `build_ext_calldata`, `run_ext_call`, `update_accounts`, and
  `update_transient` one operation at a time, and close each error branch
  immediately.
- Use available IHs and preservation/no-TypeError helpers as soon as their
  branch premises are available; avoid accumulating parallel subgoals.
- In the final concrete success-continuation branch, local specialization of the
  generated optional-driver IH is allowed if the prefix has already been split
  and its premises are concrete branch assumptions.

Still do not retry:

- `asm "driver_ih" ...` followed by broad `simp`/`gvs` over the unsplit generated
  ExtCall prefix.
- Top-level long `qspecl_then` instantiations over generated ExtCall temporaries.
- Quoted-assumption or `MATCH_MP` plumbing that reconstructs the whole prefix by
  hand.
- Helpers that merely repackage the full generated monadic prefix.
- Treating the removed tautological compact bridge as proof infrastructure.

Known remaining fresh-stack cheats remain useful context:

- `eval_all_type_sound_mutual[Expr_Call_ExtCall]`
- `eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`
- `raw_call_return_type_well_formed`

`RawCallTarget`, the localized builtin arithmetic cheat, wrapper validation,
and final validation remain downstream of ExtCall.  The immediate authorized
work is the bounded linear ExtCall proof probe described above.  If that probe
again requires broad generated-prefix reconstruction, stop and re-plan with
exact evidence.

### Completion scope

Completion for this rewrite means:

```text
holbuild build vyperSemanticsHolTheory
```

succeeds with **zero CHEAT warnings reachable from `vyperSemanticsHolTheory`**.
Old retired theories are out of scope unless they are imported transitively by
`vyperSemanticsHolTheory`.

Current build status:

```text
holbuild build vyperTypeEnvExtensionTheory       # succeeds
holbuild build vyperTypeEnvPreservationTheory    # succeeds
holbuild build vyperTypeScopePopTheory           # succeeds, no scope-pop cheat
holbuild build vyperTypeStmtSoundnessTheory      # succeeds, through the proved scope-pop layer
holbuild build vyperSemanticsHolTheory           # succeeds
```

Reachable fresh-stack cheat inventory (source audit, 2026-05-31):

```text
semantics/prop/vyperTypeBuiltinsScript.sml             1
  - raw_call_return_type_well_formed (localized arithmetic)

semantics/prop/vyperTypeStmtSoundnessScript.sml         2
  - eval_all_type_sound_mutual[Expr_Call_ExtCall]
  - eval_all_type_sound_mutual[Expr_Call_RawCallTarget]
--------------------------------------------------------
Total reachable fresh-stack cheats                    3
```

The 4 call-soundness cheats from the previous audit are now gone — `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error` in `vyperTypeCallSoundnessScript.sml` are all proved as projections from the completed mutual expression soundness theorem.

The `holbuild --strict-parse` tooling blocker is resolved; holbuild works correctly without that option.

For comparison, previous audit was 65 cheats. The reduction was achieved by:
- Proving all assignment target mutual branches (TopLevelVar Type/Value,
  Type/ArrayRef, HashMapT/HashMapRef, ImmutableVar, TupleTargetV,
  assign_targets_cons)
- Proving all assignment statement branches (AnnAssign, Assign, AugAssign)
- Proving the update-binop no-TypeError chain (well_typed_binop_no_type_error,
  well_typed_update_binop_no_type_error, assign_subscripts_update_leaf_no_type_error)
- Proving many individual builtin/structural statement cases

`vyperTypeEnvPreservationScript.sml` has no cheats.
`vyperTypeStatePreservationScript.sml` has no cheats.
`vyperTypeAssignSoundnessScript.sml` has no cheats.

No reachable cheats were found in:

```text
vyperTypeSystemScript.sml
vyperTypeValuesScript.sml
vyperTypeEnvScript.sml
vyperTypeBytesCryptoScript.sml
vyperTypeDefaultsScript.sml
vyperTypeConversionsScript.sml
vyperTypeABIScript.sml
vyperTypeExprSoundnessScript.sml
vyperTypeSoundnessNewScript.sml
vyperTypeStatePreservationScript.sml
vyperTypeEnvPreservationScript.sml
vyperTypeEnvExtensionScript.sml
vyperTypeScopePopScript.sml
vyperTypeAssignSoundnessScript.sml
```

### Completed architecture items

The following major plan items are already implemented/proved in the current
fresh stack:

- Runtime subscript refactor to value-preserving paths:
  `ValueSubscript value | AttrSubscript identifier` — **implemented in semantics**.
- Static hashmap key restriction via `hashmap_key_type`.
- `well_formed_vtype` for `Type ty` and nested `HashMapT kt vt`.
- `subscript_vtype` for arrays and hashmaps.
- Structural target-path/place bridge in `vyperTypeExprSoundnessScript.sml`,
  including:
  - `place_leaf_path_typed_evaluate`
  - `place_leaf_path_typed_array_append`
  - `place_leaf_path_typed_struct_append`
  - `place_vtype_path_typed_hashmap_root_cons`
  - `target_path_type_to_place_vtype_path_typed`
  - `target_path_type_Type_place_leaf_typed`
- All-result assignment preservation:
  - `assign_target_preserves_state_well_typed_mutual` now proves preservation
    for arbitrary `(res, st')`, not only `(INL res, st')`.
  - `assign_target_preserves_runtime_consistent`
  - `assign_targets_preserves_runtime_consistent`
  - `assign_target_preserves_runtime_consistent_result`
- Full `assign_target_sound_mutual` (all branches proved, no cheats):
  - `sound_ScopedVar`, `sound_TopLevelVar`, `sound_ImmutableVar`,
    `sound_TupleTargetV`, `sound_assign_targets_cons`
- Top-level assignment branch helpers for `HashMapRef` and `ArrayRef` paths
- Assignment statement branches (AnnAssign, Assign, AugAssign) proved
- Update-binop no-TypeError chain fully proved
- Immutable update preservation helpers factored out of the assignment proof:
  - `set_immutable_preserves_env_consistent`
  - all-result `set_immutable_preserves_state_well_typed`

### Current priority order

Completed foundational checkpoints:

- Assignability preservation proved as part of the strengthened
  `preserves_tv` frame invariant.
- Assignment target joint soundness (`assign_target_sound_mutual`) fully proved.
- Update-binop no-TypeError chain fully proved.
- Assignment statement branches (AnnAssign, Assign, AugAssign) fully proved.
- Scope-pop/env-extension reorganisation complete.

Current priority order:

1. **Bounded proof-only ExtCall probe.**  Work only in `semantics/prop`, leave
   semantics/evaluator definitions unchanged, and attempt the linear
   branch-by-branch proof of `eval_all_type_sound_mutual[Expr_Call_ExtCall]`.
   This is authorized only under the discipline above: split the monadic chain
   locally, close error cases immediately, and specialize the driver IH only in a
   concrete success-continuation branch after the prefix is discharged.
2. If the proof still requires broad simplification/specialization of the
   unsplit generated prefix, stop and re-plan with exact build/goal evidence.
3. After ExtCall succeeds, revisit
   `eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
4. Then discharge the localized builtin cheat
   `raw_call_return_type_well_formed` and rerun wrapper/final validation.

Also eventually update/replace:

- `vyperBuiltinTypingScript.sml` — currently depends on old defs/helpers. For now, mine it for reusable lemmas where appropriate, but avoid making the new final stack depend on the old soundness definitions long-term.


## Core type-system design

Use an executable statement checker:

```sml
type_stmt  : typing_env -> type -> stmt -> typing_env option
type_stmts : typing_env -> type -> stmt list -> typing_env option
```

Predicates may be wrappers around these functions, but the main preservation theorem should use the exact output env:

```sml
type_stmts env ret_ty ss = SOME env'
```

and prove:

```sml
env_consistent env' cx st'
```

### `typing_env`

Use module-aware top-level data with explicit current module:

```sml
typing_env = <|
  current_src     : num option;
  var_types       : num |-> type;
  var_assignable  : num |-> bool;
  bare_globals    : (num option # num) |-> type;
  toplevel_vtypes : (num option # num) |-> value_type;
  type_defs       : num |-> type_args;
  fn_sigs         : (num option # string) |-> fn_sig;
  flag_members    : (num option # string) |-> string list;
|>
```

- `current_src` matches runtime `current_module cx`.
- `bare_globals` contains current/module constants and immutables usable by bare name.
- `toplevel_vtypes` contains all module-qualified top-level declarations:
  - storage/transient vars: `Type ty`
  - constants/immutables: `Type ty`
  - hashmaps: `HashMapT kt vt`

`env_consistent` / function consistency should require `bare_globals` entries to agree with `toplevel_vtypes` as `Type ty` and correspond to immutable/constant declarations.

## Scoping rules

Runtime confirms scopes are local:

- `AnnAssign` adds a variable to the current top scope.
- `If` pushes a scope and pops it with `finally`.
- `For` pushes a scope with the loop variable per iteration and pops it with `finally`.

Static typing should match:

- `type_stmts` threads env sequentially.
- `AnnAssign` extends `var_types` and `var_assignable` with assignable `T`.
- `If` typechecks both branches under the input env and returns the input env; branch declarations do not escape.
- `For` typechecks body under env extended with loop var assignable `F`, but returns the input env.

## Hashmaps, subscripts, and places

### Completed subscript refactor

The runtime representation of target path subscripts has been refactored to value-preserving paths. The old inconsistent design (where `value_to_key` had no bool case and `subscript` used `IntSubscript`/`StrSubscript`/`BytesSubscript`) has been replaced with:

```sml
Datatype:
  subscript = ValueSubscript value | AttrSubscript identifier
End
```

With:

```sml
subscript_to_value (ValueSubscript v) = SOME v
subscript_to_value (AttrSubscript _) = NONE
```

Array paths use `ValueSubscript (IntV i)`. Struct field paths use `AttrSubscript id`. Hashmap paths keep the actual key value, including bool and flags.

The `value_to_key` function has been eliminated from the fresh stack. The interpreter and proof files were updated accordingly in `semantics/vyperStateScript.sml` (`compute_hashmap_slot`, `leaf_type`, `evaluate_subscripts`, `assign_subscripts`, `resolve_array_element`, `assign_target`) and downstream proof files.

Historical note: The old inconsistent design accepted bool hashmap keys for reads but rejected them for assignment targets (because `value_to_key` had no `BoolV` case), and was lossy for flags. The new design preserves the actual runtime key value.

### Hashmap key-type restriction

Static typing restricts hashmap key types to source types that are valid hashmap keys using the executable predicate:

```sml
hashmap_key_type : type -> bool
```

The exact allowed set matches Vyper and the executable encoder. With value-preserving subscripts, bool keys are supported. Arrays, tuples, structs, and `NoneT` are not accepted as hashmap key types.

Value-type well-formedness is strengthened:

```sml
well_formed_vtype tenv (Type ty) = well_formed_type tenv ty
well_formed_vtype tenv (HashMapT kt vt) =
  well_formed_type tenv kt /\
  hashmap_key_type kt /\
  well_formed_vtype tenv vt
```

and static subscript typing is strengthened:

```sml
subscript_vtype (HashMapT kt vt) idx_ty =
  if idx_ty = kt /\ hashmap_key_type kt then SOME vt else NONE
```

This prevents well-typed programs from constructing hashmap targets whose key expressions cannot be represented/encoded at runtime.

Both `hashmap_key_type` and the strengthened `well_formed_vtype`/`subscript_vtype` are implemented and used in the fresh stack.

### Place typing helpers

Keep `well_typed_expr` as first-class/materialisable expression typing. Bare hashmaps and intermediate hashmap refs must not be accepted as ordinary materialised expressions.

Use place typing helpers:

```sml
type_place_expr   : typing_env -> expr -> value_type option
type_place_target : typing_env -> base_assignment_target -> value_type option
subscript_vtype   : value_type -> type -> value_type option
```

Intended behavior after the subscript/key refactor:

- `type_place_expr (TopLevelName _ nsid)` looks up `toplevel_vtypes nsid`.
- `type_place_expr (Subscript _ e idx)` follows `subscript_vtype` when `idx` is well-typed.
- `subscript_vtype (HashMapT kt vt) idx_ty` succeeds only when `idx_ty = kt` and `hashmap_key_type kt`, returning `vt`.
- `subscript_vtype (Type (ArrayT elem bd)) idx_ty` succeeds for integer index, returning `Type elem`.
- tuple target indexing remains disabled unless/until the runtime leaf/path machinery supports it consistently.
- ordinary `well_typed_expr (Subscript ty e idx)` allows either ordinary array subscript or place/hashmap subscript whose final result is `Type ty`.
- assignment targets must end in `Type ty`, not `HashMapT`.

### Place/reference runtime typing

Do not force hashmap references into ordinary `toplevel_value_typed`. The current ordinary runtime typing says:

```sml
toplevel_value_typed (HashMapRef _ _ _ _) tyv <=> tyv = NoneTV
```

So a `HashMapRef` is not an ordinary materialised value of hashmap type. It is a runtime place/reference. Mirror the static distinction with a separate place predicate, e.g.:

```sml
toplevel_place_value_typed env tvl vt
```

Suggested shape:

```sml
toplevel_place_value_typed env (Value v) (Type ty) <=>
  ?tv. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v

toplevel_place_value_typed env (ArrayRef is_t slot elem_tv bd) (Type (ArrayT elem_ty bd')) <=>
  bd = bd' /\ evaluate_type env.type_defs elem_ty = SOME elem_tv

toplevel_place_value_typed env (HashMapRef is_t slot kt vt) (HashMapT kt' vt') <=>
  kt = kt' /\ vt = vt' /\ well_formed_vtype env.type_defs (HashMapT kt vt)
```

Expression soundness should eventually distinguish ordinary r-value typing from place/reference typing. In particular, place-expression soundness should prove:

```sml
type_place_expr env e = SOME vt /\
well_typed_expr env e /\
runtime_consistent env cx st /\
eval_expr cx e st = (INL tvl, st')
==>
toplevel_place_value_typed env tvl vt
```

### Runtime target proof relation

High-level target soundness should be structural and should not require concrete `place_leaf_typed` witnesses too early.

Use:

```sml
runtime_consistent env cx st
location_runtime_typed env cx st loc vt
target_path_typed env loc_vt sbs vt
target_runtime_typed env cx st tgt ty gv
```

where `target_runtime_typed` for a base target should package:

```sml
?loc_vt.
  location_runtime_typed env cx st loc loc_vt /\
  target_path_typed env loc_vt sbs (Type ty)
```

Prefer making the primary path relation consume paths in semantic/order-of-access order, with a raw wrapper for evaluator output:

```sml
target_path_typed_ordered env loc_vt [] vt <=> loc_vt = vt

target_path_typed_ordered env loc_vt (sb::path) vt <=>
  ?mid_vt.
    target_path_step_typed env loc_vt sb mid_vt /\
    target_path_typed_ordered env mid_vt path vt

target_path_typed env loc_vt sbs vt <=>
  target_path_typed_ordered env loc_vt (REVERSE sbs) vt
```

With value-preserving subscripts, the important path steps are conceptually:

```sml
target_path_step_typed env (Type (ArrayT elem bd)) (ValueSubscript (IntV i)) (Type elem)

target_path_step_typed env (Type (StructT s)) (AttrSubscript id) (Type field_ty) <=>
  attribute_type env.type_defs (StructT s) id = SOME field_ty

target_path_step_typed env (HashMapT kt vt) (ValueSubscript v) vt <=>
  ?ktv. evaluate_type env.type_defs kt = SOME ktv /\ value_has_type ktv v /\ hashmap_key_type kt
```

The exact array-index bounds premise can be kept separate if bounds errors are ordinary runtime errors rather than TypeErrors.

`place_leaf_typed` remains useful, but only as a lower-level assignment/state-preservation bridge from structural target paths to concrete `type_value` leaves. Do not use concrete leaf witnesses in the high-level `eval_base_target` / `target_runtime_typed` theorem statement.

After the subscript refactor, prove the concrete bridge in the assignment layer with well-formedness/runtime-consistency premises, e.g.:

```sml
runtime_consistent env cx st /\
location_runtime_typed env cx st loc loc_vt /\
target_path_typed env loc_vt sbs (Type ty)
==>
?final_tv. place_leaf_typed env loc_vt sbs ty final_tv
```

### Concrete target-path-to-leaf bridge plan

This bridge is central to assignment preservation and must cover **all** location roots, not only locals:

- `Type root_ty` roots for local variables, constants, immutables, ordinary top-level values, and arrays/structs;
- `HashMapT kt vt` roots for storage/transient hashmap references, including nested hashmaps;
- final assignment targets ending in `Type ty`.

Do **not** rely on a scoped/local-only bridge as the final architecture. It may close `ScopedVar`, but it does not justify `TopLevelVar`/storage hashmap assignment and therefore is insufficient for overall type soundness.

The useful final bridge is:

```sml
Theorem target_path_type_Type_place_leaf_typed:
  well_formed_vtype env.type_defs loc_vt /\
  target_path_type env loc_vt sbs (Type ty) ==>
  ?final_tv. place_leaf_typed env loc_vt sbs ty final_tv
```

The clean proof route is to prove the stronger internal bridge through `place_vtype_path_typed`, then specialize to `Type` endpoints:

```sml
Theorem target_path_type_to_place_vtype_path_typed:
  well_formed_vtype env.type_defs loc_vt /\
  target_path_type env loc_vt sbs vt ==>
  place_vtype_path_typed env loc_vt (REVERSE sbs) vt
```

This stronger theorem is justified because `place_vtype_path_typed` carries exactly the extra future-key obligation needed for hashmap endpoints:

```sml
place_vtype_path_typed env loc_vt path (HashMapT kt vt) <=>
  !v. place_vtype_path_typed env loc_vt (path ++ [ValueSubscript v]) vt
```

That obligation is not accidental; it is what makes the induction strong enough when a path reaches a hashmap value before the final assignment leaf.

Prove the bridge in this order.

1. Extract endpoint evaluation from concrete leaf typing:

   ```sml
   Theorem place_leaf_path_typed_evaluate:
     place_leaf_path_typed env loc_vt path ty final_tv ==>
     evaluate_type env.type_defs ty = SOME final_tv
   ```

   This follows by recursion/cases on `loc_vt` and `path`. For a `Type` root it is immediate from `place_leaf_path_typed_def`; for a `HashMapT` root, the empty path case is false and the nonempty path case peels one key and recurses.

2. Prove step-extension lemmas for `place_vtype_path_typed`.

   Hashmap step:

   ```sml
   Theorem place_vtype_path_typed_hashmap_step:
     place_vtype_path_typed env loc_vt path (HashMapT kt vt) ==>
     place_vtype_path_typed env loc_vt (path ++ [ValueSubscript key]) vt
   ```

   This is direct from `place_vtype_path_typed_def`.

   Array step should be proved through a leaf-level append lemma that works for arbitrary roots, not only `Type root_ty` roots:

   ```sml
   Theorem place_leaf_path_typed_array_append:
     place_leaf_path_typed env loc_vt path (ArrayT elem_ty len) mid_tv ==>
     ?elem_tv. place_leaf_path_typed env loc_vt
       (path ++ [ValueSubscript (IntV i)])
       elem_ty elem_tv
   ```

   Prove this by induction/cases following `place_leaf_path_typed_def`:

   - `loc_vt = Type root_ty`: use `place_leaf_path_typed_evaluate` to obtain

     ```sml
     evaluate_type env.type_defs (ArrayT elem_ty len) = SOME mid_tv
     ```

     then unfold `evaluate_type_def` for arrays and use `leaf_type_append`/`leaf_type_def`.
   - `loc_vt = HashMapT kt vt`, `path = []`: impossible by `place_leaf_path_typed_def`.
   - `loc_vt = HashMapT kt vt`, `path = sb::rest`: peel the hashmap root and apply the induction hypothesis to `vt` and `rest`; use

     ```sml
     (sb::rest) ++ [x] = sb :: (rest ++ [x])
     ```

     and unfold `place_leaf_path_typed_def` once.

   Then derive the value-type step:

   ```sml
   Theorem place_vtype_path_typed_array_step:
     place_vtype_path_typed env loc_vt path (Type (ArrayT elem_ty len)) ==>
     place_vtype_path_typed env loc_vt
       (path ++ [ValueSubscript (IntV i)])
       (Type elem_ty)
   ```

   Struct step should be proved similarly through a leaf-level append lemma:

   ```sml
   Theorem place_leaf_path_typed_struct_append:
     place_leaf_path_typed env loc_vt path (StructT s) mid_tv /\
     attribute_type env.type_defs (StructT s) id = SOME field_ty ==>
     ?field_tv. place_leaf_path_typed env loc_vt
       (path ++ [AttrSubscript id])
       field_ty field_tv
   ```

   The `Type root_ty` case uses `place_leaf_path_typed_evaluate`, `attribute_type_evaluates`, `leaf_type_append`, and `leaf_type_def`. The `HashMapT` root cases peel exactly as in the array append lemma.

   Then derive:

   ```sml
   Theorem place_vtype_path_typed_struct_step:
     place_vtype_path_typed env loc_vt path (Type (StructT s)) /\
     attribute_type env.type_defs (StructT s) id = SOME field_ty ==>
     place_vtype_path_typed env loc_vt
       (path ++ [AttrSubscript id])
       (Type field_ty)
   ```

3. Combine the step lemmas:

   ```sml
   Theorem place_vtype_path_typed_step:
     place_vtype_path_typed env loc_vt path mid_vt /\
     target_path_step_type env mid_vt sb next_vt ==>
     place_vtype_path_typed env loc_vt (path ++ [sb]) next_vt
   ```

   Prove by cases on `mid_vt` and then on the source type in the `Type` case. Hashmap, array, and struct dispatch to the step lemmas above; impossible cases are eliminated by `target_path_step_type_def`.

4. Prove reflexivity/root-shift for well-formed value types.

   Needed theorem:

   ```sml
   Theorem well_formed_vtype_place_vtype_path_typed_refl:
     well_formed_vtype env.type_defs vt ==>
     place_vtype_path_typed env vt [] vt
   ```

   The risky case is `HashMapT kt vt`, because reflexivity requires all possible future keys:

   ```sml
   !key. place_vtype_path_typed env (HashMapT kt vt) [ValueSubscript key] vt
   ```

   Prove a root-shift helper rather than trying to fake hashmap reflexivity with a local special case:

   ```sml
   Theorem place_vtype_path_typed_hashmap_root_cons:
     place_vtype_path_typed env vt path endpoint ==>
     place_vtype_path_typed env (HashMapT kt vt)
       (ValueSubscript key :: path)
       endpoint
   ```

   This should be proved by structural induction/cases on `endpoint`, using the `Type` endpoint definition of `place_leaf_path_typed` and the hashmap endpoint universal-key clause of `place_vtype_path_typed`. Then use it with the IH for the inner `vt` to prove the hashmap reflexivity case.

   If this helper needs strengthening, strengthen it generally, not with a one-off theorem specialized to `[]` or a single hashmap layer. The required semantic fact is that adding a concrete hashmap key in front of the concrete path shifts the root from `vt` to `HashMapT kt vt`.

5. Prove the general structural bridge:

   ```sml
   Theorem target_path_type_to_place_vtype_path_typed:
     well_formed_vtype env.type_defs loc_vt /\
     target_path_type env loc_vt sbs vt ==>
     place_vtype_path_typed env loc_vt (REVERSE sbs) vt
   ```

   Induct on `sbs`:

   - base: `target_path_type_def` gives `loc_vt = vt`; use `well_formed_vtype_place_vtype_path_typed_refl`;
   - step: use the IH on the recursive `target_path_type`, then `place_vtype_path_typed_step`; `REVERSE (sb::sbs) = REVERSE sbs ++ [sb]`.

6. Derive the assignment-facing bridge:

   ```sml
   Theorem target_path_type_Type_place_leaf_typed:
     well_formed_vtype env.type_defs loc_vt /\
     target_path_type env loc_vt sbs (Type ty) ==>
     ?final_tv. place_leaf_typed env loc_vt sbs ty final_tv
   ```

   This is immediate from `target_path_type_to_place_vtype_path_typed`, `place_leaf_typed_def`, and the `Type` case of `place_vtype_path_typed_def`.

#### Bridge risk review

The main possible failure points are now localized and checkable:

1. `place_vtype_path_typed_hashmap_root_cons` may need a stronger induction statement. This is proof-engineering risk, not an architecture mismatch: semantically, `place_leaf_path_typed` for `HashMapT` explicitly peels the first concrete path element.
2. Array extension depends on extracting the element evaluation from `evaluate_type env.type_defs (ArrayT elem_ty len) = SOME mid_tv`. This should follow from `evaluate_type_def`; all array side conditions are already encoded in the successful evaluation assumption.
3. Struct extension depends on `attribute_type_evaluates`. This theorem already provides the needed evaluated field type and runtime field lookup.
4. The old mistake was proving only a `Type`-endpoint IH. That fails when the recursive midpoint is `HashMapT kt vt`. The general `place_vtype_path_typed` bridge avoids that by carrying hashmap future-key obligations through the induction.

If any of these fail, stop and reassess the definitions. Do not replace the bridge with a scoped-only theorem, because that would leave overall assignment/type soundness incomplete.

Already proved useful rebuild lemmas in `vyperTypeStatePreservationScript.sml` may need to be updated to the structural target predicate:

```sml
target_runtime_typed_rebuild
target_assignment_values_typed_rebuild
```

These rebuild target typing in a later state from `runtime_consistent`; they are essential for tuple assignment tails.

## Assignment preservation (completed) and proof engineering lessons

The assignment preservation theorem has been strengthened to the all-result
mutual statement and all branches of `assign_target_sound_mutual` are proved.
The update-binop no-TypeError chain is also fully proved.

```sml
assign_target_preserves_state_well_typed_mutual
```

Despite the historical name, its statement preserves the full invariant:

```sml
runtime_consistent env cx st'
```

for arbitrary `assign_target`/`assign_targets` evaluations:

```sml
assign_target cx gv op st = (res, st')
assign_targets cx gvs vs st = (res, st')
```

not only successful `(INL ..., st')` results. Public success-only corollaries are
now weaker wrappers. The formerly cheated all-result corollary is proved:

```sml
assign_target_preserves_runtime_consistent_result
```

This strengthening was the right architecture: tuple/list assignment can perform
partial successful prefix updates before a later failure, so the proof must use
the mutual induction principle directly rather than a separate success/error
layer.

### Important semantic change already made

`semantics/vyperStateScript.sml` was changed so augmented assignment evaluates binops using the leaf runtime type:

```sml
assign_subscripts tv a [] (Update ty bop v) =
  let u = case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0 in
    evaluate_binop u tv bop a v
```

Previously this used `NoneTV`, which made type preservation false/unprovable.

Immediate fallout already fixed:

- `semantics/prop/vyperLookupScript.sml` theorem `assign_target_name_update` now states the update in terms of the actual `scope_entry.type`.
- `assign_operation_runtime_typed` for `Update` now treats the constructor type as the target/result type and existentially recovers the RHS type:

```sml
assign_operation_runtime_typed env ty (Update target_ty bop v) <=>
  target_ty = ty /\
  ?rhs_ty. value_runtime_typed env rhs_ty v /\ well_typed_binop ty bop ty rhs_ty
```

Useful operation-to-leaf lemmas already proved:

```sml
place_leaf_typed_evaluate_type
assign_operation_leaf_replace
assign_operation_leaf_append
assign_operation_leaf_update
```

`AppendOp` is now typed only for dynamic arrays:

```sml
ty = ArrayT elem_ty (Dynamic n)
```

## Scope-pop/env-extension reorganisation (completed)

The foundational blocker `scope_bracket_preserves_ec` has been proved and the
clean split is in place.  The final organisation is:

```text
vyperTypeEnvExtension
  Static typing-env extension/weakening and env-map well-formedness facts.
  This is a low-level static-env theory and must not depend on
  vyperTypeEnvPreservation or statement soundness.

vyperTypeEnvPreservation
  Generic frame-style preservation of env consistency.

vyperTypeScopePop
  Runtime pushed-scope execution, pop, and restoration of outer env consistency.
  This should depend on vyperTypeEnvExtension plus evaluator/state preservation
  facts.  It should not depend on statement soundness.

vyperTypeStmtSoundness
  Statement/list/for-loop no-TypeError and result/postcondition proof layer.
```

Preferred dependency graph:

```text
vyperTypeSystem / vyperTypeValues / vyperTypeEnv
        ↓
vyperTypeEnvExtension
        ↓
vyperTypeEnvPreservation
        ↓
expression / assignment / other frame users

vyperTypeEnvExtension + vyperEvalPreservesScopes + vyperStatePreservation
        ↓
vyperTypeScopePop
        ↓
vyperTypeStmtSoundness
        ↓
vyperTypeCallSoundness
        ↓
vyperTypeSoundnessNew
        ↓
vyperSemanticsHol
```

`vyperTypeScopePop` should not import `vyperTypeEnvPreservation` unless a
specific theorem from it is genuinely needed; the intended scope-pop proof can
be done from env extension, evaluator scope facts, and `preserves_tv` facts.

### `vyperTypeEnvExtensionScript.sml` responsibilities

Status: complete.  This theory has been created, the generic static-env facts
have been moved/factored out of `vyperTypeEnvPreservationScript.sml` and
`vyperTypeStmtSoundnessScript.sml`, and `vyperTypeEnvExtensionTheory` builds.

It owns:

```sml
env_maps_wf_def
env_consistent_env_maps_wf
env_maps_wf_no_stale_assignable_T

env_extends_def
env_extends_refl
env_extends_trans

extend_local_preserves_static
type_stmt_preserve_nonlocal_fields
type_stmts_preserve_nonlocal_fields

(* Compatibility names may be kept as aliases, or downstream references updated. *)
type_stmt_env_preserved_static
type_stmts_env_preserved_static
type_stmt_env_consistent_preserved_static
type_stmts_env_consistent_preserved_static

type_stmt_var_types_preserve
type_stmts_var_types_preserve
type_stmt_var_types_mono
type_stmts_var_types_mono

type_stmt_var_assignable_T_preserve
type_stmts_var_assignable_T_preserve

type_stmt_env_maps_wf
type_stmts_env_maps_wf

type_stmt_env_extends
type_stmts_env_extends
```

This theory should depend only on the executable type-system definitions and
basic env definitions, not on statement soundness and not on
`vyperTypeEnvPreservation`.

Because `env_maps_wf_def` moves here, every fresh theory using `env_maps_wf`
should import `vyperTypeEnvExtension` directly rather than relying on
`vyperTypeEnvPreservation` to provide it transitively.

### `vyperTypeScopePopScript.sml` responsibilities

Status: complete for the current reorganisation.  This theory has been created,
the generic scope-pop helpers have been moved/factored out of
`vyperTypeStmtSoundnessScript.sml`, `scope_bracket_preserves_ec` is proved with
the final intended strengthened shape, and `vyperTypeScopePopTheory` builds.

It owns:

```sml
push_scope_env_consistent
pop_scope_env_consistent
push_scope_with_var_env_consistent

env_extends_env_consistent_after_pop
type_stmts_env_consistent_after_pop
eval_stmts_pushed_scope_env_consistent_after_pop
scope_bracket_preserves_ec
scope_bracket_preserves_swt
```

Do **not** move `env_extends_return_exception_typed` into this lower theory for
now.  It depends on statement-level exception/result typing definitions
(`return_exception_typed_def`) and should remain in `vyperTypeStmtSoundness` unless
that result-typing layer is later factored out separately.

`scope_bracket_preserves_ec` must have the stable final precondition
`env_consistent env cx st`, not merely `st.scopes <> []`:

```sml
Theorem scope_bracket_preserves_ec:
  env_maps_wf env /\
  env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  env_consistent env_after cx st_body /\
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  (!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
```

This shape is required for type soundness because it supplies all three facts
needed by the pop proof:

1. original scopes are nonempty;
2. old env variables are visible in the pre-state, so they cannot be introduced
   as new variables in the pushed head;
3. variables newly present in `env_after` but absent from `env` are absent from
   the original tail and therefore cannot escape after the pop.

The proof is a wrapper around `type_stmts_env_consistent_after_pop`, with its
premises proved explicitly as named facts before applying the theorem.  This was
important proof engineering: applying the pop theorem too early left unmanaged
parallel subgoals and made the final tail-escape case fragile.  Do **not** try
to prove `env_consistent env cx st_body` before popping; that can be false
because variables declared in the pushed runtime head are visible in `st_body`
but absent from the outer static env.  Instead prove the popped target directly:

- case-split `st_body.scopes = h::tl`; the empty case contradicts scope-length
  preservation from evaluation under `sc::st.scopes` plus pre-state env
  consistency;
- get `tl <> []` from `env_consistent env cx st` and
  `eval_stmts_preserves_scopes_len`;
- prove old env variables are absent from the final head using
  `lookup_scopes_not_in_new_head` and the pushed-scope side condition;
- prove old assignable variables are absent from the final head by combining
  `env_maps_wf` with the previous old-variable argument;
- prove new `env_after` variables do not escape into the tail using
  `eval_stmts_preserves_tail_lookup_none` plus pre-state env consistency;
- prove the required frame fact with
  `eval_stmts_scope_bracket_gen_preserves_tv` and the statement-list component
  of `eval_preserves_tv`.

### `vyperTypeStmtSoundnessScript.sml` cleanup

Status: complete for the current reorganisation checkpoint.  Statement
soundness now imports `vyperTypeEnvExtension` and `vyperTypeScopePop`; duplicate
moved generic definitions/theorems have been removed.  Statement-specific result
and postcondition facts remain there, including
`env_extends_return_exception_typed`.

`scope_bracket_preserves` should remain a statement-level orchestration helper
but be strengthened to require the pre-state env consistency needed by
`scope_bracket_preserves_ec`:

```sml
Theorem scope_bracket_preserves:
  env_maps_wf env /\
  env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
  state_well_typed st_body /\
  env_consistent env_after cx st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts
```

Fresh statement-soundness call sites already operate under pre-state runtime/env
consistency, so this strengthening matches the final type-soundness invariant.
The common block-scope case uses `sc = FEMPTY`, so the side condition
`!id. id IN FDOM env.var_types ==> id NOTIN FDOM sc` is trivial there.  For
loop/prepopulated scopes, the side condition states the required non-shadowing of
existing static env variables.

### Build checkpoints for the reorganisation

Checkpoint status:

```sh
holbuild build vyperTypeEnvExtensionTheory       # passed
holbuild build vyperTypeEnvPreservationTheory    # passed
holbuild build vyperTypeScopePopTheory           # passed, no scope-pop cheat
holbuild build vyperTypeStmtSoundnessTheory      # passed through the proved scope-pop layer
holbuild build vyperSemanticsHolTheory           # passed
```

The scope-pop reorganisation is complete through the public aggregator.  This is
a foundational step, not the whole soundness proof: the later
ABI/builtin/expression-assignability/assignment-no-TypeError, statement, and
call cheats must still be discharged for the final `vyperSemanticsHolTheory`
no-cheat completion target.

Non-ABI builtin TODOs that say the executable type system must be strengthened
remain a possible definition-level risk and must be audited before claiming final
non-ABI type soundness.  Treat those as specification/definition obligations,
not merely proof-script cleanup.

### Lessons from the all-result assignment proof

#### Strengthen the mutual theorem, do not layer decompositions

For mutually recursive semantics such as:

```sml
assign_target ... TupleTargetV ... -> assign_targets ...
assign_targets ... -> assign_target ...; assign_targets ...
```

prove the strong all-result mutual invariant directly. Avoid a separate stack of
success theorem + error theorem + combined theorem. The direct mutual proof was
simpler and handled partial tuple/list updates naturally.

#### Control subgoals aggressively

Do not let simplification produce unmanaged parallel goals. Do not use `>|` or
`THENL`. Preferred patterns:

```sml
... >> tactic_for_one_focused_goal
... >- branch_for_first_goal
reverse $ gvs[...]
NO_TAC  (* temporary checkpoint only, to confirm there is exactly one subgoal *)
```

Avoid generated-name-dependent scripts such as `Cases_on `tv`` after a large
`gvs[AllCaseEqs()]`: the displayed variable may not be a stable script-level
name. Instead normalize with case-rator theorems and solve one focused branch at
a time:

```sml
gvs[Once assign_target_def, bind_def, return_def, raise_def,
    lift_option_def, lift_option_type_def, lift_sum_def,
    AllCaseEqs(), option_CASE_rator, sum_CASE_rator,
    toplevel_value_CASE_rator]
```

#### Use exact preservation helpers for state updates

For branches that update only one component of the state, factor the preservation
obligation instead of reconstructing a large invariant inline. The immutable case
introduced:

```sml
set_immutable_preserves_env_consistent
set_immutable_preserves_state_well_typed
```

Important: `env_consistent` helpers often need static environment links, not just
runtime value typing. For immutable updates, the helper must carry:

```sml
FLOOKUP env.bare_globals (env.current_src,n) = SOME ty
.evaluate_type (get_tenv cx) ty = SOME tv
```

whereas `state_well_typed` needs runtime facts such as:

```sml
value_has_type tv v
well_formed_type_value tv
```

Do not confuse these two proof obligations.

#### Branches ending in `assign_result`

For assignment branches that write/update state and then call `assign_result`,
prove the invariant for the post-write state first and then use:

```sml
assign_result_preserves_state
```

This avoids assuming the final result is `INL`.

#### Tuple/list assignment pattern

`TupleTargetV` should use the strengthened list IH directly. Construct the
`target_assignment_values_typed` witness from tuple typing facts using:

```sml
LIST_REL3_from_LIST_REL2
LIST_REL3_EL
target_values_runtime_typed_LIST_REL3
```

The `assign_targets_cons` case is the key partial-update pattern:

1. Use the first-target IH to get `runtime_consistent` for the intermediate
   state, regardless of result shape.
2. If the first target succeeds and the tail runs, rebuild tail typing in the
   updated state with:

   ```sml
   target_assignment_values_typed_rebuild
   ```

3. Apply the list IH to the tail.

This is the canonical pattern for any future recursive/list evaluator
preservation proof.

#### Top-level assignment pattern

The `TopLevelVar` case is best handled by normalizing the semantic branch and
using existing read/write/storage preservation lemmas immediately. Avoid trying
to destruct the pretty-printed `tv` variable after a broad simplification.
Storage array `AppendOp`/`PopOp` are multi-write cases; chain write preservation
facts explicitly.

### Build commands

Use:

```sh
holbuild build vyperTypeStatePreservationTheory
holbuild build vyperSemanticsHolTheory
```

The first should be used during assignment-preservation work; the second verifies
downstream fallout and the final completion target.  `--new-ir` is deprecated and
has no effect.

## Defaults

Internal-call default expressions are evaluated at call time after pushing `(src_id_opt, fn)` onto `cx.stk`, but before `bind_arguments`/`push_function`. Therefore defaults:

- may refer to constants/immutables in the callee module;
- cannot refer to parameters or local variables.

Typing rule: check defaults under the function-body env with locals cleared:

```sml
env_default = env_body with <| var_types := FEMPTY; var_assignable := FEMPTY |>
```

Do not erase globals/toplevels/type defs/flag members/function signatures unless intentionally restricting defaults further.

## Deferred self-contained builtin gaps

The following issues are intentionally deferred during the current derisking
phase, but they remain final obligations.  Keep the existing comments/cheats as
markers rather than prematurely reshaping the whole proof around them.

### ABI encode known gap

ABI encode success typing is blocked by a missing static bound. Current typing of ABI encode permits result type:

```sml
BaseT (BytesT (Dynamic n))
```

but does not require `n` to be large enough for the encoded output.

This is a correctness-risk item, not merely a documentation note.  Before the
reachable final theorem can be cheat-free, choose and implement one of:

1. add static encoded-size bounds strong enough to prove success typing;
2. exclude or specially weaken AbiEncode success typing in the relevant theorem
   shapes while retaining no-TypeError soundness; or
3. prove that the current runtime/result typing does not require the missing
   bound.

Do not prioritize this until the broader assignment/target/statement/call proof
structure has been validated, unless it unexpectedly blocks that work.

### `MsgGas` / other isolated builtin gaps

`Env MsgGas` and other self-contained builtin proof gaps should likewise be left
as explicit comments/cheats for now.  They are expected to be local runtime/type
or arithmetic/encoding obligations.  They must be fixed before final completion,
but should not drive near-term architecture work unless an audit shows that a
supposedly local builtin gap actually affects theorem shapes outside the builtin
layer.

## Soundness theorem shapes

The proof should distinguish **no-TypeError** from **successful evaluation**. Many well-typed operations can still fail with runtime errors (bounds, overflow, ABI decoding, unavailable block hash, etc.). Therefore most semantic helper theorems should not claim existential success.

Preferred theorem pattern:

```sml
(* No static type failure. RuntimeError/Assert/Return/etc. may still occur. *)
well_typed_... /\ invariants ==> !msg. evaluator ... <> INR (Error (TypeError msg))

(* If evaluation succeeds, the returned value has the expected type. *)
well_typed_... /\ invariants /\ evaluator ... = INL v ==> value_has_type expected_tv v
```

Use existential-success theorems only for operations that genuinely cannot fail under the stated hypotheses. Examples where existential success is too strong:

- `Env PrevHash`: may return `RuntimeError` depending on block hash availability.
- `Env MsgGas`: currently has a static type but no runtime `evaluate_builtin` case; either exclude it in no-TypeError lemmas or fix runtime semantics later.
- `Len`: runtime expression evaluation special-cases `Len` through `toplevel_array_length`; generic `evaluate_builtin` does not implement `Len`.
- `AbiDecode`, `Extract32`, conversions, bounded arithmetic, and many external/special calls can fail with non-TypeError runtime errors.

For `Len`, the useful local invariant is:

```sml
evaluate_type tenv arg_ty = SOME arg_runtime_tv /\
well_formed_type_value arg_runtime_tv /\
toplevel_value_typed arg_tv arg_runtime_tv /\
toplevel_array_length cx arg_tv st = (INL n, st')
==>
n < dimword(:256)
```

The `well_formed_type_value` fact is mathematically necessary because `toplevel_value_typed`/`value_has_type` alone does not rule out ill-formed runtime descriptors such as oversized `BytesT (Fixed n)`. In expression soundness this should normally be derived from `evaluate_type_well_formed_type_value`.

The master theorem should prove mutually over evaluator functions:

- `state_well_typed` preservation,
- `env_consistent` preservation using the executable checker output env,
- `accounts_well_typed` preservation,
- no `Error (TypeError s)`,
- return-value typing,
- expression result typing (`toplevel_value_typed`) and materialised value typing.

The final public theorem can wrap the executable checker predicates as needed, but the proof should use the stronger `type_stmts env ret ss = SOME env'` form.

## Proof style notes

- Prefer one active subgoal at a time.
- Avoid broad tactics that leave many unrelated subgoals open.
- Do not use `THENL`; prefer helper lemmas or careful `>-` / `conj_tac >- ... >> ...` structure.
- Split large builtin/type-builtin proofs into no-TypeError and success-type lemmas, with per-constructor helpers where branches have genuinely different mathematical arguments.
