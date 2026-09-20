# TASK: Prove checked constant-evaluation output typing authority

## Meta
Status: planned
Priority: P1
Created: 2026-09-20
Location: `semantics/prop`

## Theorem Statements (FROZEN)

```sml
Theorem checked_initial_immutables_constants_input_tags_agree:
  check_contract F layouts target mods = SOME artifact /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms ==>
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods
    (am with immutables updated_by CONS (target,imms))
Proof
  cheat
QED

Theorem checked_evaluate_all_constants_output_typed:
  check_contract F layouts target mods = SOME artifact /\
  (cx.in_deploy ==>
    ?deploy_art. check_contract T layouts target mods = SOME deploy_art) /\
  cx.layouts = layouts /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot layouts target /\
  get_tenv cx = type_env_all_modules mods /\
  machine_well_typed am /\
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods am /\
  context_well_typed cx /\
  ALOOKUP cx.sources target = SOME mods /\
  cx.txn.target = target /\
  evaluate_all_constants cx am target mods = SOME am_c ==>
  deployment_constants_output_typed
    (type_env_all_modules mods) target mods am_c
Proof
  cheat
QED

Theorem checked_deployment_constants_ready_from_success:
  check_contract F layouts target mods = SOME artifact /\
  (cx.in_deploy ==>
    ?deploy_art. check_contract T layouts target mods = SOME deploy_art) /\
  cx.layouts = layouts /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot layouts target /\
  get_tenv cx = type_env_all_modules mods /\
  machine_well_typed am /\
  deployment_constants_input_tags_agree
    (type_env_all_modules mods) target mods am /\
  context_well_typed cx /\
  ALOOKUP cx.sources target = SOME mods /\
  cx.txn.target = target /\
  evaluate_all_constants cx am target mods = SOME am_c ==>
  checked_deployment_constants_ready cx am target mods
Proof
  cheat
QED
```

Relevant existing definitions:

```sml
Definition deployment_constants_input_tags_agree_def:
  deployment_constants_input_tags_agree tenv addr mods
      (am:abstract_machine) <=>
    !src ts vis mut id ty init tv v.
      MEM (src,ts) mods /\
      MEM (VariableDecl vis mut id ty init) ts /\
      (mut = Immutable \/ ?e. mut = Constant e) /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am.immutables addr of
           | SOME imms => imms
           | NONE => []))
        (string_to_num id) = SOME (tv,v) ==>
      evaluate_type tenv ty = SOME tv
End

Definition deployment_constants_output_typed_def:
  deployment_constants_output_typed tenv addr mods (am:abstract_machine) <=>
    EVERY (\(stored_addr, imms). imms_well_typed imms) am.immutables /\
    !src ts vis e id ty init.
      MEM (src,ts) mods /\
      MEM (VariableDecl vis (Constant e) id ty init) ts ==>
      ?tv v.
        FLOOKUP
          (get_source_immutables src
            (case ALOOKUP am.immutables addr of
             | SOME imms => imms
             | NONE => []))
          (string_to_num id) = SOME (tv,v) /\
        evaluate_type tenv ty = SOME tv /\
        value_has_type tv v
End

Definition checked_deployment_constants_ready_def:
  checked_deployment_constants_ready cx am addr mods <=>
    IS_SOME (evaluate_all_constants cx am addr mods) /\
    !am_c.
      evaluate_all_constants cx am addr mods = SOME am_c ==>
      deployment_constants_output_typed (get_tenv cx) addr mods am_c
End
```

**These corrected statements replace the original counterexampled pair. Do not modify them.** Prove them as-is, or produce a new counterexample.

## Completion Criteria

1. `holbuild vyperTypeContractSoundnessTheory` from the repository root passes with zero CHEAT warnings and zero FAILs.
2. Add only focused helper lemmas needed by these proofs, preferably in the existing target theory; do not create new libraries or theories.
3. Prove that the ordinary `initial_immutables` setup establishes the new input tag-agreement condition.
4. The stored value for every checked constant is proved with `value_has_type`, not only runtime type-tag equality.
5. Do not make further interpreter changes; `constants_env` has already been aligned with `evaluate_defaults` by using `[FEMPTY]`.
6. Existing namespace, source-order, and source-identity authority is reused rather than duplicated in consumers.
7. The convenience theorem is derived from successful output typing and evaluator determinism.

**If any theorem is false as stated:**
- Produce a HOL4 counterexample where practical.
- State the tightest sufficient fix.
- Do not silently weaken the statement.

## Build

```sh
cd /home/ramana/vyper-hol-dev
holbuild vyperTypeContractSoundnessTheory
```

## Background

Issue #504 requests a public checker-backed bridge from successful whole-contract constant evaluation to the complete deployment constant typing predicate. Existing local lemmas establish that constants remain present with the runtime tag returned by `evaluate_type`, but they do not establish `value_has_type` for the stored value.

The original frozen theorem was formally counterexampled: `machine_well_typed` relates values only to their stored tags, so it permits a pre-existing bare-global entry whose tag disagrees with its checked declaration. The corrected theorem adds `deployment_constants_input_tags_agree`, which supplies exactly that missing cross-layer agreement without requiring unevaluated constants to be present. Do not retry or generalize from the obsolete counterexampled statement.

`constants_env` now evaluates initializers from `initial_state ... [FEMPTY]`, following the `evaluate_defaults` resolution in issue #473. This removes the former empty-scope obstruction to applying expression soundness.

The source file contains comments immediately above the frozen theorems explaining why the corrected statements should hold and the intended mathematical invariant.

## Domain Constraints

- Do not make further changes to `constants_env`, `evaluate_all_constants`, or other interpreter semantics.
- Never replace or delete an existing proof in favor of `cheat`.
- Final proofs must contain no cheats and produce no CHEAT warnings.
- Use `holbuild` for proof feedback; do not use interactive `g()`, `e()`, or `p()` workflows.
- Keep the development local and focused. Add helper lemmas only when a repeated or difficult subgoal warrants one; do not introduce new libraries, theories, tactics, conversions, or other general infrastructure for this task.
- Avoid broad or repeated `metis_tac` searches and recursive-definition simplification that causes proof explosion.
- Do not depend on automatically generated variable names; use explicit renaming where necessary.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target source | `semantics/prop/vyperTypeContractSoundnessScript.sml` | Frozen theorems, existing constant-presence/type-tag lemmas, and checker authority |
| Readiness definitions | `semantics/prop/vyperTypeEntryReadinessScript.sml` | `deployment_constants_output_typed`, `checked_deployment_constants_ready`, and setup lemmas |
| Interpreter semantics | `semantics/vyperInterpreterScript.sml` | `constants_env`, `merge_constants`, `set_current_module`, and `evaluate_all_constants` |
| Expression soundness | `semantics/prop/vyperTypeEvalSoundnessScript.sml` | `eval_all_type_sound_mutual`; conjunct 8 gives successful expression result typing |
| Expression result predicates | `semantics/prop/vyperTypeExprSoundnessScript.sml` | `expr_result_typed`, `value_runtime_typed`, and `value_has_type` bridge definitions |
| Runtime invariants | `semantics/prop/vyperTypeInvariantsScript.sml` | `imms_well_typed`, `state_well_typed`, `env_consistent`, `functions_well_typed`, and `context_well_typed` |
| Initial-state machinery | `semantics/prop/vyperTypeInitialStateScript.sml` | `machine_well_typed`, initial-state typing, immutable readiness and preservation lemmas |
| Checker definitions | `semantics/type/vyperTypeContractScript.sml` | `check_contract`, constant declaration checking, namespaces, and artifact construction |
| Static checker facts | `semantics/prop/vyperTypeContractStaticMapsScript.sml` | Checker-derived declaration, namespace, static-map, and module uniqueness results |
| Context consistency | `semantics/prop/vyperTypeContractContextScript.sml` | Checker-to-environment/context consistency bridges |
| Function typing | `semantics/prop/vyperTypeContractFunctionScript.sml` | Runtime/deployment `functions_well_typed` results |
| Call-graph safety | `semantics/prop/vyperTypeCallGraphSoundnessScript.sml` | Checked call-graph safety authority for expression evaluation |
| Comparable list proof | `semantics/prop/vyperTypeEntryReadinessScript.sml` | `evaluate_defaults_success_values_typed` applies expression soundness over an evaluator list |
| Proof-control guidance | `docs/HOL4_PROOF_CONTROL_LESSONS.md` | Project-specific branch and induction proof practices |
| Repository rules | `AGENTS.md` | Required HOL4 workflow and proof conventions |
| Issue | `https://github.com/verifereum/vyper-hol/issues/504` | Requested theorem surface and acceptance criteria |
