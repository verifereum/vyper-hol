# Vyper Type System Rewrite Plan

Goal: replace the current messy `vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, and `vyperTypeSoundness` development with a fresh, executable type system and clean soundness proof stack.

## Requirements

The new development should provide:

1. **Executable type checking** — statement/program typing should be computable by `EVAL`.
2. **No-TypeError soundness** — well-typed evaluation never returns `INR (Error (TypeError s))`.
3. **Result correctness / preservation** — expression results, materialised values, returns, state, env consistency, and accounts remain well-typed.

## Strategy

Do not mutate the old proof stack in place. Build new theories with new names, then switch over and delete/retire the old theories once complete.

Current fresh theory stack:

- `vyperTypeSystemScript.sml` — new executable type-system definitions.
- `vyperTypeValuesScript.sml` — pure value/type lemmas.
- `vyperTypeEnvScript.sml` — env/state/scope/immutable consistency lemmas.
- `vyperTypeEnvPreservationScript.sml` — frame-style env consistency preservation lemmas.
- `vyperTypeBytesCryptoScript.sml` — bytes/crypto value typing helpers.
- `vyperTypeDefaultsScript.sml` — default argument typing helpers.
- `vyperTypeConversionsScript.sml` — conversion typing helpers.
- `vyperTypeABIScript.sml` — ABI typing helpers.
- `vyperTypeBuiltinsScript.sml` — clean replacement for builtin/type-builtin/binop facts.
- `vyperTypeExprSoundnessScript.sml` — expression/iterator/target no-TypeError and preservation theorem layer.
- `vyperTypeStatePreservationScript.sml` — state-update, scope, materialisation, assignment preservation lemmas.
- `vyperTypeStmtSoundnessScript.sml` — statement/statement-list no-TypeError and preservation theorem layer.
- `vyperTypeCallSoundnessScript.sml` — call-entry and internal/external/special call theorem layer.
- `vyperTypeSoundnessNewScript.sml` — final public theorem surface.

The aggregator `vyperSemanticsHolScript.sml` has been switched to import `vyperTypeSoundnessNew` rather than the old final theory.

Eventually replace:

- `vyperTypeSoundnessDefsScript.sml`
- `vyperTypeSoundnessHelpersScript.sml`
- `vyperTypeSoundnessScript.sml`

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

## Hashmaps and places

Keep `well_typed_expr` as first-class/materialisable expression typing. Bare hashmaps and intermediate hashmap refs must not be accepted as ordinary expressions.

Place typing helpers:

```sml
type_place_expr   : typing_env -> expr -> value_type option
type_place_target : typing_env -> base_assignment_target -> value_type option
subscript_vtype   : value_type -> type -> value_type option
```

Current intended behavior:

- `type_place_expr (TopLevelName _ nsid)` looks up `toplevel_vtypes nsid`.
- `type_place_expr (Subscript _ e idx)` follows `subscript_vtype` when `idx` is well-typed.
- `subscript_vtype (HashMapT kt vt) idx_ty` succeeds when `idx_ty = kt`, returning `vt`.
- `subscript_vtype (Type (ArrayT elem bd)) idx_ty` succeeds for integer index, returning `Type elem`.
- ordinary `well_typed_expr (Subscript ty e idx)` allows either ordinary array/tuple subscript or place/hashmap subscript whose final result is `Type ty`.
- assignment targets must end in `Type ty`, not `HashMapT`.

### Runtime target proof relation

The old shape-only relation was too weak. The current clean design is state-aware and place-based:

```sml
runtime_consistent env cx st
location_runtime_typed env cx st loc vt
place_leaf_typed env vt sbs ty final_tv
target_runtime_typed env cx st tgt ty gv
```

Key points:

- `runtime_consistent` bundles `env_consistent`, `state_well_typed`, `context_well_typed`, and `accounts_well_typed`.
- `location_runtime_typed` returns a `value_type`, not a `type_value`:
  - locals and immutables are `Type ty` roots;
  - top-level locations use `env.toplevel_vtypes` directly, so `HashMapT kt vt` roots are supported.
- `place_leaf_typed` connects a value-type root plus runtime subscripts to the static assignment leaf type and runtime leaf `type_value`.
- `target_runtime_typed env cx st tgt ty gv` combines static target typing, runtime shape, location typing, and leaf typing.

Already proved useful rebuild lemmas in `vyperTypeStatePreservationScript.sml`:

```sml
target_runtime_typed_rebuild
target_assignment_values_typed_rebuild
```

These rebuild target typing in a later state from `runtime_consistent`; they are essential for tuple assignment tails.

## Assignment preservation status and next-agent instructions

Current critical theorem:

```sml
assign_target_preserves_state_well_typed_mutual
```

Despite the historical name, its statement now preserves the full invariant:

```sml
runtime_consistent env cx st'
```

for both `assign_target` and `assign_targets`. Public corollaries derive state/account preservation from runtime consistency.

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

### Remaining suspended cases

Run:

```sh
grep -n "Resume assign_target_preserves_state_well_typed_mutual\|cheat" semantics/prop/vyperTypeStatePreservationScript.sml
```

Expected remaining cases:

```sml
ScopedVar
TopLevelVar
ImmutableVar
TupleTargetV
```

`assign_targets_cons` is already proved.

### Suggested proof strategy for remaining cases

General pattern for `ScopedVar` and `ImmutableVar`:

1. Unfold `assign_target_def` and monadic combinators.
2. Extract the current root type/value from runtime lookup.
3. Use `target_runtime_typed_def`, `location_runtime_typed_def`, and `place_leaf_typed` to get the static/runtime leaf typing.
4. Prove the new assigned value has the original root type using:

   ```sml
   assign_subscripts_preserves_type
   assign_operation_leaf_replace
   assign_operation_leaf_update
   assign_operation_leaf_append
   ```

   For `PopOp`, `assign_subscripts_preserves_type` has no extra premise.
5. Prove `state_well_typed` after the update:
   - locals: use `scope_well_typed_update_value` / `update_name_preserves_state_well_typed` or inline `find_containing_scope_structure`.
   - immutables: use/adapt old helper facts if needed, but copy into the new stack rather than importing old soundness helpers.
6. Prove `env_consistent` after the update using frame preservation:

   ```sml
env_consistent_preserved_by_frame
   ```

   You will need frame facts for scopes/immutables and assignability preservation. Existing env-preservation lemmas include:

   ```sml
lookup_scopes_fupdate_other
lookup_scopes_append_cons
lookup_scopes_append_fupdate_other
update_name_preserves_assignable_lookup
materialise_preserves_assignable_lookup
get_Value_preserves_assignable_lookup
   ```

General pattern for `TupleTargetV`:

- Unfold `assign_target_def` for tuple replace.
- Use `target_runtime_typed_def` to get tuple static/shape info.
- Use `target_assignment_values_typed_def` and `LIST_REL3` alignment.
- Apply `assign_targets_preserves_runtime_consistent` / the list IH.

General pattern for `TopLevelVar`:

- Do not try to prove one giant inline branch. Split by `lookup_global` result:
  - `Value v`
  - `ArrayRef is_transient base_slot elem_tv bd`
  - `HashMapRef is_transient base_slot kt vt`
- Recommended helper lemmas:

```sml
assign_toplevel_value_preserves_runtime_consistent
assign_toplevel_arrayref_preserves_runtime_consistent
assign_toplevel_hashmapref_preserves_runtime_consistent
```

- The value-type based `location_runtime_typed` now supports both `Type ty` and `HashMapT kt vt` top-level roots, so there should be no remaining design blocker.
- Use storage helpers already proved:

```sml
read_storage_slot_success_type
materialise_preserves_type
write_storage_preserves_state_well_typed
set_storage_preserves_state_well_typed
set_storage_preserves_accounts_well_typed
```

- Hashmap branch likely needs facts about:

```sml
split_hashmap_subscripts
compute_hashmap_slot
read_storage_slot
write_storage_slot
```

If this branch becomes large, state the exact branch goal as a helper theorem and prove it separately.

### Build commands

Use:

```sh
holbuild build --new-ir vyperTypeStatePreservationTheory
holbuild build --new-ir vyperSemanticsHolTheory
```

The first should be used during assignment-preservation work; the second verifies downstream fallout.

## Defaults

Internal-call default expressions are evaluated at call time after pushing `(src_id_opt, fn)` onto `cx.stk`, but before `bind_arguments`/`push_function`. Therefore defaults:

- may refer to constants/immutables in the callee module;
- cannot refer to parameters or local variables.

Typing rule: check defaults under the function-body env with locals cleared:

```sml
env_default = env_body with <| var_types := FEMPTY; var_assignable := FEMPTY |>
```

Do not erase globals/toplevels/type defs/flag members/function signatures unless intentionally restricting defaults further.

## ABI encode known gap

ABI encode success typing remains intentionally skipped/blocked by a missing static bound. Current typing of ABI encode permits result type:

```sml
BaseT (BytesT (Dynamic n))
```

but does not require `n` to be large enough for the encoded output. Leave this as a known design gap unless explicitly asked to fix ABI bounds.

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
