# TASK: Fresh Vyper type-system soundness rewrite

## Goal

Complete the fresh Vyper type-system soundness stack.

Final completion criterion:

```sh
holbuild build vyperSemanticsHolTheory
```

must succeed with **zero CHEAT warnings reachable from `vyperSemanticsHolTheory`**.

## Source of truth / context

Read these first, in this order:

1. This task file.
2. `TYPE_SYSTEM_REWRITE_PLAN.md` — teammate-authored durable reference and latest handover notes.
3. `PLAN_type_system_rewrite.md` — Alan working PLAN seed. This may be rewritten/rendered by `plan_oracle`; do not treat later PLAN rewrites as replacing `TYPE_SYSTEM_REWRITE_PLAN.md`.

Current SML source is authoritative for internal theorem statements unless this task explicitly freezes a public obligation below.

## Frozen / non-frozen statements

Frozen public behavior:

- Well-typed evaluation must not return `Error (TypeError s)`.
- Successful/exceptional results must preserve the appropriate state/env/account/runtime typing invariants.
- The public fresh surface in `semantics/prop/vyperTypeSoundnessNewScript.sml` must continue to expose wrappers equivalent in strength to:
  - `typed_stmts_no_type_error`
  - `typed_stmts_success_preserves_state_env`
  - `typed_stmts_exception_preserves_state_and_return_type`
  - `typed_expr_no_type_error`
  - `typed_expr_success_preserves_type`
  - `typed_callable_body_no_type_error`

Not frozen:

- Internal helper theorem statements in assignment/statement/call/builtin layers may be strengthened, renamed, replaced, or turned into compatibility corollaries when required by the strongest-joint-invariant architecture.
- If an existing cheated theorem is false or underspecified, do not force it through. Prove a stronger/correct joint theorem and update callers, or close a stuck/probe episode with evidence before changing architecture.

## In-scope fresh theories

Focus only on theories reachable from `vyperSemanticsHolTheory` in the fresh stack, especially:

- `semantics/prop/vyperTypeStatePreservationScript.sml`
- `semantics/prop/vyperTypeAssignSoundnessScript.sml`
- `semantics/prop/vyperTypeStmtSoundnessScript.sml`
- `semantics/prop/vyperTypeCallSoundnessScript.sml`
- `semantics/prop/vyperTypeBuiltinsScript.sml`
- strict prerequisite fresh-stack theories needed to discharge those obligations.

Old retired theories (`vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, `vyperTypeSoundness`) are out of scope unless they are still imported transitively by `vyperSemanticsHolTheory`.

## Current handover-sensitive obligations

The pulled 2026-05-13 plan update supersedes the older “state preservation has no cheats” note. Current focused work is assignment-target soundness in `vyperTypeStatePreservationScript.sml`.

Known build-through cheats/scaffolding from the latest handover:

### `vyperTypeStatePreservationScript.sml`

Inside `assign_target_sound_mutual`:

- `sound_TopLevelVar`: `HashMapRef` case
- `sound_TopLevelVar`: `ArrayRef` case
- `sound_ImmutableVar`
- `sound_TupleTargetV`
- `sound_assign_targets_cons`

Do not weaken `assign_target_sound_mutual` to remove its strengthened side conditions. Prove the missing branches/helpers.

### `vyperTypeStmtSoundnessScript.sml`

Assignment statement cases need updates after assignment preservation was strengthened to require:

```sml
assign_operation_matches_target_shape gv op
assign_target_assignable_context cx gv st
```

Affected branches include:

- `eval_all_type_sound_mutual[AnnAssign]`
- `eval_all_type_sound_mutual[Assign]`
- `eval_all_type_sound_mutual[AugAssign]`

Missing statement-level obligations:

1. Derive `assign_operation_matches_target_shape` for the operation being performed.
2. Derive `assign_target_assignable_context` for evaluated targets, including scoped assignability and top-level storage/hashmap writability.
3. For `AnnAssign`, use `assignable_type` to derive non-`NoneT` side conditions.
4. For tuple/list assignment, use `target_assignment_values_assignable` to feed typedness plus assignability/context side conditions.

### Inherited update-binop path cheats

Known inherited path:

- `well_typed_binop_no_type_error`
- `well_typed_update_binop_no_type_error`
- `assign_subscripts_update_leaf_no_type_error`
- `assign_operation_runtime_typed_leaf_no_type_error`
- `assign_subscripts_no_type_error_runtime_typed`
- `assign_subscripts_preserves_type_runtime_typed`

Treat these as localized builtin/binop obligations unless they block assignment/statement architecture.

### Older wrapper/builtin/call obligations

Still in scope if reachable:

- assignment compatibility wrappers in `vyperTypeAssignSoundnessScript.sml`:
  - `assign_target_no_type_error`
  - `assign_target_update_no_type_error`
  - `assign_target_append_no_type_error`
- builtin/binop/type-builtin cheats in `vyperTypeBuiltinsScript.sml`, including ABI encode bound and `Env MsgGas` issues.
- call wrappers in `vyperTypeCallSoundnessScript.sml`:
  - `internal_call_no_type_error`
  - `internal_call_type_preservation`
  - `external_call_no_type_error`
  - `special_call_no_type_error`
- remaining suspended/cheated cases inside `eval_all_type_sound_mutual`.

## Architectural constraints

1. Prove the strongest joint invariant following evaluator recursion.
2. Do not duplicate evaluator case analysis across parallel no-TypeError/preservation proof trees.
3. If a property is needed downstream, strengthen the existing mutual/frame invariant instead of starting a second induction over the same evaluator.
4. Assignment soundness should be joint and all-result where the evaluator can partially update state before later failure.
5. Preserve the current fresh-stack split:
   - static env extension facts in `vyperTypeEnvExtension`
   - frame-style env consistency in `vyperTypeEnvPreservation`
   - pushed-scope/pop restoration in `vyperTypeScopePop`
   - evaluator statement soundness in `vyperTypeStmtSoundness`
6. Use `holbuild`; do not use direct HOL.
7. If a theorem appears false, create/prove a small probe or close a stuck episode with evidence before changing architecture.

## Recommended first actions for Alan

1. Read `TYPE_SYSTEM_REWRITE_PLAN.md`, especially “Assignment target soundness progress update (2026-05-13)”.
2. Run/inspect `holbuild build vyperTypeStatePreservationTheory` and then `holbuild build vyperSemanticsHolTheory` to confirm current source status.
3. Use `plan_oracle` to migrate/augment `PLAN_type_system_rewrite.md` into structured components and risks.
4. Start with the focused assignment-target branches before broad statement/builtin cleanup:
   - `TopLevelVar` `HashMapRef`
   - `TopLevelVar` `ArrayRef`
   - `ImmutableVar`
   - `TupleTargetV`
   - `assign_targets_cons`
5. Then repair statement assignment branches by deriving the strengthened assignment side conditions.

## Done definition

- `holbuild build vyperSemanticsHolTheory` succeeds.
- There are zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.
- Any internal theorem statement changes are justified by the joint-invariant architecture and reflected in callers.
- Deferred builtin issues are either proved, repaired by executable typing/runtime changes, or explicitly shown not to affect the final public theorem surface.
