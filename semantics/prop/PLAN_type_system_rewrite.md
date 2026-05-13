# PLAN: Fresh Vyper type-system soundness rewrite

This is an initial Alan PLAN seed. `plan_oracle` may rewrite/render this file into structured components. The teammate-authored reference and latest handover remain in `TYPE_SYSTEM_REWRITE_PLAN.md`.

## Scope and completion

Task: discharge all reachable fresh-stack cheats needed for:

```sh
holbuild build vyperSemanticsHolTheory
```

with zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.

The pulled 2026-05-13 handover changed the tactical priority: `vyperTypeStatePreservationScript.sml` now contains intentional build-through cheats in the strengthened assignment mutual theorem. Start there before broad statement/builtin cleanup.

## Global strategy

Follow the strongest-joint-invariant principle:

- evaluator-recursive proofs should jointly prove no-TypeError, state preservation, env consistency, accounts preservation, result/exception typing, assignability/frame facts, and result-specific typing;
- split public wrappers are allowed only after the joint theorem exists;
- compatibility no-TypeError lemmas should not drive the architecture;
- if a theorem is false/underspecified, repair the invariant or theorem shape rather than forcing brittle proof scripts.

Proof engineering discipline from the handover:

- one active semantic branch at a time;
- avoid broad `gvs[..., AllCaseEqs(), ...]` followed by cleanup of many parallel goals;
- split exactly where the evaluator branches;
- use exact branch helper lemmas before trying inline proof scripts;
- do not use `THENL`; prefer focused `>-` branches or helper theorems.

## Components

### C1: Refresh audit and structured coverage

Kind: `audit`
Risk: 2
Dependencies: none
Checkpoint: yes

#### Description
Confirm the current reachable cheat inventory after the pull and ensure every task-scoped unfinished proof is covered by a structured component.

#### Approach
- Build `vyperTypeStatePreservationTheory` and `vyperSemanticsHolTheory`.
- Grep current fresh-stack source for `cheat`/`suspend`; ignore old retired theories unless they are imported by the fresh final stack.
- Treat `TYPE_SYSTEM_REWRITE_PLAN.md` 2026-05-13 assignment-target update as higher priority than older 2026-05-12 inventory notes.
- Classify obligations as:
  - strengthened assignment mutual theorem branch;
  - statement-level side-condition derivation;
  - compatibility wrapper from a stronger theorem;
  - localized builtin/binop/runtime-support issue;
  - call/expression wrapper issue;
  - false/underspecified theorem needing a probe.

#### Outputs
- Structured coverage for all reachable cheats.
- Updated risk/frontier if the current source differs from this seed plan.

---

### C2: Assignment mutual theorem — `TopLevelVar` `HashMapRef` branch

Kind: `proof`
Risk: 3
Dependencies: C1
Checkpoint: yes

#### Description
Prove the `HashMapRef` branch currently cheated in:

```sml
assign_target_sound_mutual[sound_TopLevelVar]
```

in `vyperTypeStatePreservationScript.sml`.

#### Current context
The `Value` branch of `sound_TopLevelVar` is already proved. The current proof shape ends with:

```sml
Cases_on `tv` >- (Value branch proved) >>
gvs[]
>- cheat (* HashMapRef case *)
>> cheat (* ArrayRef case *)
```

#### Approach
Do not prove inline first. State a focused helper lemma for the `HashMapRef` semantic branch and inspect it with `NO_TAC`/holbuild if needed.

Expected fact sequence from `TYPE_SYSTEM_REWRITE_PLAN.md`:

1. Use `assign_target_assignable_context` to obtain `sbs <> []` and top-level hashmap slot availability.
2. Use successful lookup/consistency facts, e.g. `lookup_global_HashMapRef` or local equivalent plus `top_level_HashMap_decl`, to connect returned `HashMapRef is_transient base_slot kt vt` to the declaration and `HashMapT kt vt` target vtype.
3. Use strengthened `target_path_type` hashmap-key invariant: `ValueSubscript key`, `hashmap_key_type kt`, successful key type evaluation, and `value_has_type`.
4. After hashmap prefix traversal, reduce the suffix assignment to:

   ```sml
   assign_subscripts_no_type_error_runtime_typed
   ```

   with a leaf bridge analogous to `top_level_storage_value_leaf_evaluate_type`, but rooted at the hashmap value type after `split_hashmap_subscripts`.
5. Rule out storage read/write TypeErrors using `read_storage_slot_error` and typed write helpers such as `write_storage_slot_no_type_error_from_value_has_type`, or a focused set/write helper.

#### Not to try
- Do not weaken `assign_target_sound_mutual` or drop `assign_target_assignable_context`.
- Do not destruct broad generated state after large simplification; eliminate impossible declaration/lookup cases early with exact lemmas.

---

### C3: Assignment mutual theorem — `TopLevelVar` `ArrayRef` branch

Kind: `proof`
Risk: 3
Dependencies: C1, C2
Checkpoint: yes

#### Description
Prove the `ArrayRef` branch currently cheated in:

```sml
assign_target_sound_mutual[sound_TopLevelVar]
```

#### Approach
First state exact branch helper lemmas; do not prove the branch inline directly.

Expected obligations:

1. Storage-array `AppendOp` branch.
2. Storage-array `PopOp` branch.
3. Ordinary element/path assignment through `resolve_array_element` or equivalent array-reference traversal.
4. Recursive suffix assignment no-TypeError via:

   ```sml
   assign_subscripts_no_type_error_runtime_typed
   ```

5. Typed storage write-back no-TypeError via existing storage write helpers.

#### Not to try
- Do not conflate dynamic-array append/pop with ordinary element assignment.
- Chain multi-write preservation facts explicitly for storage array operations.

---

### C4: Assignment mutual theorem — immutable, tuple, and list recursion branches

Kind: `proof`
Risk: 3
Dependencies: C1, C2, C3
Checkpoint: yes

#### Description
Remove remaining build-through cheats in `assign_target_sound_mutual`:

- `sound_ImmutableVar`
- `sound_TupleTargetV`
- `sound_assign_targets_cons`

#### Approach
Immutable branch:

- Use existing immutable update preservation helpers:
  - `set_immutable_preserves_env_consistent`
  - `set_immutable_preserves_state_well_typed`
- Keep static env links (`FLOOKUP env.bare_globals ...`, evaluated type) separate from runtime typing facts (`value_has_type`, `well_formed_type_value`).

Tuple/list branches:

- Use the strengthened mutual/list IH directly.
- For tuple target value witnesses use:
  - `LIST_REL3_from_LIST_REL2`
  - `LIST_REL3_EL`
  - `target_values_runtime_typed_LIST_REL3`
- For `assign_targets_cons`:
  1. first-target IH gives `runtime_consistent` for the intermediate state regardless of result shape;
  2. if first target succeeds and tail runs, rebuild tail typing with `target_assignment_values_typed_rebuild`;
  3. apply list IH to the tail.

#### Not to try
- Do not introduce a success-only assignment theorem layer.
- Do not rebuild tuple/list state preservation from scratch outside the mutual theorem.

---

### C5: Statement assignment side-condition repair

Kind: `proof_architecture`
Risk: 4
Dependencies: C2, C3, C4
Checkpoint: yes

#### Description
Repair statement assignment branches after assignment preservation was strengthened to require:

```sml
assign_operation_matches_target_shape gv op
assign_target_assignable_context cx gv st
```

Affected branches include:

- `eval_all_type_sound_mutual[AnnAssign]`
- `eval_all_type_sound_mutual[Assign]`
- `eval_all_type_sound_mutual[AugAssign]`

#### Approach
Prove statement-level side-condition lemmas rather than weakening assignment soundness:

1. Derive `assign_operation_matches_target_shape` for each operation (`Replace`, `Update`, `AppendOp`, `PopOp`) from statement typing and evaluated target shape.
2. Derive `assign_target_assignable_context` for evaluated targets:
   - scoped assignability from env/scope consistency;
   - top-level storage/hashmap writability from declaration/layout facts;
   - tuple/list contexts from per-target facts.
3. For `AnnAssign`, use:

   ```sml
   assignable_type
   assignable_type_not_NoneT
   assignable_type_evaluate_not_NoneTV
   ```

   to remove local non-`NoneT` cheats.
4. For tuple/list assignment, use `target_assignment_values_assignable` to feed typedness plus assignability/context side conditions.
5. Rebuild target typing across intermediate states using existing rebuild lemmas when expression/materialisation evaluation changes state.

#### Not to try
- Do not patch statement branches by weakening `assign_target_sound_mutual`.
- Do not resurrect old `assign_target_*_no_type_error` wrappers as the primary proof path.

---

### C6: Remaining statement mutual soundness cases

Kind: `proof`
Risk: 4
Dependencies: C5
Checkpoint: yes

#### Description
Discharge remaining suspended/cheated cases inside `eval_all_type_sound_mutual` using one strengthened mutual theorem, not split proof trees.

#### Approach
- Work one evaluator branch at a time.
- Use completed lower layers:
  - `vyperTypeEnvExtension`
  - `vyperTypeEnvPreservation`
  - `vyperTypeScopePop`
  - assignment soundness from C2-C5.
- For pushed scopes, use the proven scope-pop layer and prove the popped target directly.

#### Not to try
- Do not prove separate no-TypeError and preservation inductions over statements.
- Do not prove `env_consistent env cx st_body` before popping a pushed scope; that can be false.

---

### C7: Compatibility wrappers in `vyperTypeAssignSoundnessScript.sml`

Kind: `compatibility_wrapper`
Risk: 2
Dependencies: C2, C3, C4, C5
Checkpoint: no

#### Description
Discharge or replace old assignment no-TypeError wrappers:

- `assign_target_no_type_error`
- `assign_target_update_no_type_error`
- `assign_target_append_no_type_error`

#### Approach
- Prefer deriving these as corollaries from the strengthened assignment mutual theorem.
- If current wrappers are stale/too weakly stated, update callers to use the joint theorem directly and keep only needed public compatibility corollaries.

---

### C8: Builtin/binop/type-builtin localized cleanup

Kind: `proof`
Risk: 3
Dependencies: C1
Checkpoint: no

#### Description
Discharge localized builtin/binop/type-builtin cheats after architecture-sensitive assignment/statement/call structure is validated, unless a builtin fact blocks earlier work.

#### Obligations include

- `well_typed_binop_no_type_error`
- `well_typed_binop_success_type`
- `well_typed_builtin_app_no_type_error`
- suspended/cheated cases in `well_typed_builtin_app_success_type`
- `well_typed_type_builtin_no_type_error`
- suspended/cheated cases in `well_typed_type_builtin_success_type`
- inherited update-binop path cheats:
  - `well_typed_update_binop_no_type_error`
  - `assign_subscripts_update_leaf_no_type_error`
  - `assign_operation_runtime_typed_leaf_no_type_error`
  - `assign_subscripts_no_type_error_runtime_typed`
  - `assign_subscripts_preserves_type_runtime_typed`

#### Approach
- Split per constructor where branches have genuinely different mathematics.
- Preserve no-TypeError vs success-typing distinction.
- Treat ABI encode bound and `Env MsgGas` as specification/runtime-support obligations.

#### Not to try
- Do not claim existential success for operations that can legitimately fail with non-TypeError runtime errors.
- Do not let ABI/`MsgGas` reshape assignment/statement architecture unless they actually block it.

---

### C9: Call soundness wrappers and call/expression integration

Kind: `proof`
Risk: 3
Dependencies: C6, C8
Checkpoint: yes

#### Description
Prove call no-TypeError/type-preservation obligations using statement/expression joint soundness and function/default-argument typing facts.

#### Obligations

- `internal_call_no_type_error`
- `internal_call_type_preservation`
- `external_call_no_type_error`
- `special_call_no_type_error`

#### Approach
- For internal calls, route through callable-function lookup, default typing, argument binding, pushed function/scope setup, and `eval_stmts` soundness.
- Defaults use function-body env with locals cleared:

  ```sml
  env_default = env_body with <| var_types := FEMPTY; var_assignable := FEMPTY |>
  ```

- For external/special calls, distinguish no-TypeError from runtime errors.
- Preserve split wrappers as public API only.

---

### C10: Final public surface and zero-cheat verification

Kind: `integration`
Risk: 2
Dependencies: C6, C7, C8, C9
Checkpoint: yes

#### Description
Verify the final public theorem surface and remove/retire any remaining reachable cheats.

#### Approach
- Build `vyperSemanticsHolTheory`.
- Confirm no reachable CHEAT warnings.
- Confirm `vyperTypeSoundnessNewScript.sml` still exposes the public theorem surface required by the task.
- If old retired theories are still imported transitively, either remove the dependency or prove only the strict prerequisite needed by the fresh stack.

#### Outputs
- `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable CHEAT warnings.
- The final public wrappers retain the task-required behavior.

## Deferred notes from teammate reference

Final obligations, but not near-term architecture drivers unless they block C2-C6:

- ABI encode static bound issue.
- `Env MsgGas` / runtime support for `MsgGas`.
- Other isolated builtin arithmetic/encoding details.

Keep comments/cheats as markers until architecture-sensitive components are derisked; then discharge them before claiming final completion.
