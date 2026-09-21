# TASK: Prove the focused constant pure-expression typing boundary

## Task identity

This is a new, single-checkpoint task. Do not resume any previous Alan state.

- Baseline commit: `97b34765e`
- Branch: `dev`
- Permitted source file:
  `semantics/prop/vyperTypeContractSoundnessScript.sml`
- Build target: `vyperTypeContractSoundnessTheory`

Do not inspect or copy work from archived branches or `.alan/archive*` state.
Create fresh state files using the task name `constant_pure_expr_typing` if
persistence is required.

## Scope

Prove only the focused typing theorem for successful evaluation of a checked
constant expression.

Stop after this theorem builds. Do **not** begin proofs about `constants_env`,
`evaluate_all_constants`, `deployment_constants_output_typed`, or the two final
cheated theorems.

## Current checker boundary

At baseline `97b34765e`, `constant_expr` permits only:

- a `TopLevelName` that denotes a declared constant;
- `Literal`;
- recursively constant `StructLit`;
- recursively constant `Subscript` (both base and index);
- recursively constant `Attribute`;
- approved compile-time `Builtin` applications;
- approved compile-time `TypeBuiltin` applications.

It rejects `Name`, `FlagMember`, `IfExp`, `Pop`, `Call`, runtime environment and
account reads, unsupported builtins, unsafe arithmetic, and unsupported type
builtins.

Do not change the checker or interpreter.

## Existing focused infrastructure

Reuse the local results already present immediately before the frozen output
theorems in `vyperTypeContractSoundnessScript.sml`, including:

```sml
deployment_constant_cells_typed
deployment_constant_cells_typed_initial
deployment_constant_cells_typed_lookup
constant_top_level_name_pure_typed
constant_literal_pure_typed
eval_pure_exprs_success_typed
eval_pure_named_exprs_success_typed
OPT_MMAP_expr_types_from_LIST_REL_local
OPT_MMAP_evaluate_type_mono_local
struct_lit_ZIP_length_local
struct_has_type_ZIP_same_names_local
struct_lit_expr_result_typed_local
```

`constant_flag_member_pure_typed` is obsolete because `FlagMember` is no longer
a `constant_expr`. Do not use or generalize it.

Also reuse the exported builtin typing theorems rather than proving individual
builtin cases:

```sml
vyperTypeBuiltinsTheory.well_typed_builtin_app_success_type
vyperTypeBuiltinsTheory.well_typed_type_builtin_success_type
```

Use existing subscript and attribute typing lemmas where their statements match.
Do not reproduce the full evaluator-soundness proof.

## Required result

Prove one task-local theorem, with a name such as
`constant_pure_eval_success_typed`, establishing the following mathematical
boundary:

- the contract checks successfully;
- the context points at the checked modules and type environment;
- the input machine is well typed;
- present declared constant cells satisfy `deployment_constant_cells_typed`;
- the state is `initial_state am [FEMPTY]`;
- `constant_expr mods e`;
- `well_typed_expr (artifact_env artifact mods current_src) e`;
- `eval_pure_expr cx (initial_state am [FEMPTY]) e = SOME tvl`;

imply:

```sml
expr_result_typed (artifact_env artifact mods current_src) e tvl /\
?v. tvl = Value v
```

The exact quantifier order may follow `eval_pure_expr_ind` or
`constant_expr_ind`. The theorem may be mutual with an expression-list result
if required, but its exported/local consumer must have the boundary above.

The list conclusion should be no stronger than:

```sml
exprs_runtime_typed env es vs
```

under successful `eval_pure_exprs`, recursive constant-expression premises, and
`well_typed_exprs`.

## Proof approach

1. Align induction with `constant_expr` or `eval_pure_expr` recursion.
2. Close `TopLevelName` and `Literal` with existing local helpers.
3. Close `StructLit` through the existing named-list and struct packaging
   boundaries.
4. For `Subscript` and `Attribute`, prove only successful `Value` result typing.
   Use the fact that both recursive operands are constant expressions. Do not
   develop general storage/place evaluator soundness.
5. For `Builtin` and `TypeBuiltin`, use the public success-type theorems listed
   above after obtaining recursively typed argument values.
6. Constructor cases excluded by `constant_expr` must close by simplification.

If static `Subscript` typing presents ordinary and place-expression alternatives,
carry the minimum task-local result needed for the recursive base. Do not infer
or prove a global equivalence between the two judgments.

## Mutation and architecture prohibitions

Do not modify any other `.sml` file. In particular, do not modify:

- `vyperTypeStatePreservationScript.sml`;
- `vyperTypeEvalSoundnessScript.sml`;
- `vyperEvalPureExprScript.sml`;
- `vyperTypeContractScript.sml`;
- interpreter definitions.

Do not add infrastructure about:

- assignment or storage writes;
- account preservation;
- function calls;
- evaluator modes;
- immutable completion;
- lookup refinement/simulation;
- general evaluator soundness;
- `constants_env` or whole-contract iteration.

## Budgets and mandatory escalation

Relative to baseline `97b34765e`:

- at most **300 new source lines**;
- at most **6 new helper theorems/definitions**;
- the central structural or mutual proof may be at most **150 lines**;
- every other individual proof should remain below 50 lines.

Stop and report the exact goal before crossing any budget.

Also stop immediately if:

1. another `.sml` file appears necessary;
2. a forbidden architecture above appears necessary;
3. two materially different attempts leave the same unresolved goal;
4. the required theorem appears false;
5. a frozen final theorem would need to change;
6. a commit would not be build-clean.

Escalation—not generalization—is the required response to a stop condition.

## Git discipline

Before every commit run:

```sh
git diff --name-only 97b34765e
```

Only this task file/state documentation and
`semantics/prop/vyperTypeContractSoundnessScript.sml` may appear.

Do not commit:

- `FAIL_TAC` probes;
- temporary cheats;
- modifications to the two existing final cheats;
- a non-building theory.

## Completion

Run:

```sh
holbuild vyperTypeContractSoundnessTheory
```

This checkpoint is complete only when:

1. the new focused pure-expression typing theorem is proved;
2. the theory builds;
3. no new cheat or `FAIL_TAC` was added;
4. only the permitted proof file was modified;
5. Alan stops without beginning `constants_env` or final-theorem work.

The two pre-existing final cheats are outside this checkpoint and may remain.
