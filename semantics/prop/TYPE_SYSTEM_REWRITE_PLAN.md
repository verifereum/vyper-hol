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
- `vyperTypeBuiltinsScript.sml` — clean replacement for builtin/type-builtin/binop facts.
- `vyperTypeStatePreservationScript.sml` — state-update, scope, materialisation, assignment preservation lemmas.
- `vyperTypeExprSoundnessScript.sml` — expression/iterator/target no-TypeError and preservation theorem layer.
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

Add place typing helpers:

```sml
type_place_expr   : typing_env -> expr -> value_type option
type_place_target : typing_env -> base_assignment_target -> value_type option
subscript_vtype   : value_type -> type -> value_type option
```

Recommended behavior:

- `type_place_expr (TopLevelName _ nsid)` looks up `toplevel_vtypes nsid`.
- `type_place_expr (Subscript _ e idx)` follows `subscript_vtype` when `idx` is well-typed.
- `subscript_vtype (HashMapT kt vt) idx_ty` succeeds when `idx_ty = kt`, returning `vt`.
- `subscript_vtype (Type (ArrayT elem bd)) idx_ty` succeeds for integer index, returning `Type elem`.
- ordinary `well_typed_expr (Subscript ty e idx)` allows either ordinary array/tuple subscript or place/hashmap subscript whose final result is `Type ty`.
- assignment targets must end in `Type ty`, not `HashMapT`.

## Defaults

Internal-call default expressions are evaluated at call time after pushing `(src_id_opt, fn)` onto `cx.stk`, but before `bind_arguments`/`push_function`. Therefore defaults:

- may refer to constants/immutables in the callee module;
- cannot refer to parameters or local variables.

Typing rule: check defaults under the function-body env with locals cleared:

```sml
env_default = env_body with <| var_types := FEMPTY; var_assignable := FEMPTY |>
```

Do not erase globals/toplevels/type defs/flag members/function signatures unless intentionally restricting defaults further.

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
