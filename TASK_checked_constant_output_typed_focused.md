# TASK: Finish checked constant output typing — focused pure-evaluator proof

## Identity and baseline

This is a **new task**, not a continuation of any earlier Alan task.

- Start commit: `724821b3e`
- Preparation/checker boundary: `1b8238986`
- Do not read or resume old `STATE`, `PLAN`, `DOSSIER`, or `LEARNINGS` files.
- Do not inspect or copy proof code from `archive`, `archive2`, or other archived branches.

The earlier attempts pursued general evaluator and assignment preservation. Those
architectures are abandoned for this issue.

## Goal

Remove the cheats from exactly these two frozen theorems in
`semantics/prop/vyperTypeContractSoundnessScript.sml`:

- `checked_evaluate_all_constants_output_typed`
- `checked_deployment_constants_ready_from_success`

Do not change their statements.

The already-proved theorem
`checked_initial_immutables_constants_input_tags_agree` is complete and must not
be reworked.

## Existing focused boundary — reuse it

The checker now requires `constant_expr mods e` for constant initializers.
These public bridge theorems are already proved:

```sml
constant_expr_pure
checked_constant_initializer_pure
checked_constant_initializer_eval_pure
```

The current branch also contains focused local infrastructure immediately above
the frozen theorem:

```sml
deployment_constant_cells_typed
deployment_constant_cells_typed_initial
deployment_constant_cells_typed_lookup
constant_top_level_name_pure_typed
constant_literal_pure_typed
constant_flag_member_pure_typed
```

Review and reuse these results. Do not replace them with a more general global
invariant.

## Required proof route

1. Prove a focused typing result for successful `eval_pure_expr` evaluation of
   `constant_expr` expressions from `initial_state am [FEMPTY]`.
2. Use it in an induction over `constants_env`, maintaining only typed constant
   cells and machine typing needed by later initializers.
3. Induct over `evaluate_all_constants` and reuse existing presence, tag,
   namespace, source-order, and non-clobber lemmas.
4. Establish `deployment_constants_output_typed`.
5. Derive `checked_deployment_constants_ready_from_success` from the first
   theorem and evaluator determinism.

If the pure-expression proof needs both ordinary and place typing for recursive
`Subscript`/`Attribute` cases, a task-local mutual lemma is permitted. It must
remain confined to pure expressions and successful results.

## Strict mutation boundary

Unless the owner explicitly approves otherwise, modify only:

```text
semantics/prop/vyperTypeContractSoundnessScript.sml
```

You may update this task's fresh state notes, but do not modify any other `.sml`
file. In particular, do not modify:

- `vyperTypeStatePreservationScript.sml`
- `vyperTypeEvalSoundnessScript.sml`
- `vyperEvalPureExprScript.sml`
- checker or interpreter definitions

Existing theorems from those theories may be reused without modification.

## Mandatory stop-and-escalate gates

Stop immediately and report the exact goal and attempted theorem if any of the
following occurs:

1. You believe another `.sml` file must be modified.
2. You believe you need a theorem about assignment, storage writes, accounts
   preservation, calls, evaluator modes, immutable completion, lookup
   refinement, or general evaluator soundness.
3. The focused pure-expression development would exceed **300 new lines beyond
   start commit `724821b3e`**.
4. More than **10 new helper theorems/definitions** are needed beyond those
   already present at the start commit.
5. A single proof exceeds 50 lines; first propose the exact helper lemma, and
   stop if splitting it would cross either preceding budget.
6. A theorem statement appears false or requires strengthening a frozen
   theorem premise.
7. Two consecutive proof attempts expose essentially the same unresolved goal.
8. The branch is not build-clean at a commit boundary.

Do not respond to a stop condition by generalizing the evaluator or adding
infrastructure. Escalation is the required result.

## Git and state discipline

- Before every commit, run:
  ```sh
  git diff --name-only 724821b3e
  ```
  It must list only `semantics/prop/vyperTypeContractSoundnessScript.sml` and
  fresh task-state documentation.
- Never describe a diff as pre-existing without verifying it against
  `724821b3e`.
- Do not commit `FAIL_TAC`, probes, temporary cheats, or a non-building theory.
- Keep commits small and build-clean.
- Do not reuse old task state. Create fresh state files with a distinct
  `focused` task name if state persistence is required.

## Completion criteria

Run:

```sh
holbuild vyperTypeContractSoundnessTheory
```

Completion requires:

1. the build passes;
2. no `FAIL_TAC` remains;
3. both target cheats are removed;
4. no CHEAT warnings remain for the target theory;
5. only the permitted source file was modified;
6. every checked constant output has both the declared runtime tag and
   `value_has_type`.

## Useful existing resources

- `semantics/prop/vyperEvalPureExprScript.sml`
  - `eval_pure_expr_def`
  - `eval_expr_to_eval_pure_expr_some`
  - `eval_pure_expr_to_eval_expr_some`
- `semantics/prop/vyperTypeEntryReadinessScript.sml`
  - output/readiness predicates
  - comparable list-evaluation typing proofs
- `semantics/prop/vyperTypeContractStaticMapsScript.sml`
  - checker-derived namespace and declaration authority
- `semantics/prop/vyperTypeContractSoundnessScript.sml`
  - constant presence/tag/non-clobber lemmas and the focused starting helpers
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`
- `AGENTS.md`
