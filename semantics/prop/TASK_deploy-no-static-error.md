# TASK: checked deployment reaches the constructor body with no static error

## Meta
Status: planned
Priority: P1
Created: 2026-10-21
Location: semantics/prop

## Theorem Statement (FROZEN)

```sml
Theorem checked_load_contract_no_static_error:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  context_well_typed cx /\
  LENGTH tx.args = LENGTH args /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  ?imms am_c scope.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    evaluate_all_constants cx
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps)|>)
      tx.target mods = SOME am_c /\
    bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
    args_values_typed (type_env_all_modules mods) args tx.args /\
    load_contract orc am tx mods exps =
      (case call_external_body orc am_c cx nr mut (type_env_all_modules mods)
              scope body ret of
         (INR e, _, _) => INR e
       | (INL _, am', rqs) =>
           INL (finalize_pending_deletions
                  (am' with sources updated_by CONS (tx.target,mods)), rqs)) /\
    no_type_error_result
      (FST (call_external_body orc am_c cx nr mut (type_env_all_modules mods)
              scope body ret)) /\
    !exc.
      FST (call_external_body orc am_c cx nr mut (type_env_all_modules mods)
             scope body ret) = INR exc ==>
      exc <> BreakException /\ exc <> ContinueException
```

`call_external_body` is defined in `semantics/prop/vyperTypeSelectedEntrySoundnessScript.sml`;
`no_type_error_result` in `semantics/prop/vyperTypeExprSoundnessScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The other theorems in `vyperTypeDeploymentSoundnessScript.sml` (`check_contract_initial_immutables`,
`check_contract_constructor_no_defaults`, `checked_constructor_bind_arguments`,
`load_contract_constructor_body`) are weakly frozen:
use them, prove more helpers, but don't change their statements.

## Completion Criteria

1. `holbuild -j4 build vyperTypeDeploymentSoundnessTheory` passes from the project root with zero CHEAT warnings and zero failures.
2. No new definitions, axioms, or premises; no `cheat` anywhere.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; never raise the tactic timeout.
4. Proofs at most ~50 lines each (repo AGENTS.md); split into helper lemmas.
5. Existing theorem statements elsewhere unchanged. Dropping `[local]` from an existing lemma in
   `semantics/prop/vyperTypeContractSoundnessScript.sml` is allowed if you need it; otherwise prefer adding
   helpers in `vyperTypeDeploymentSoundnessScript.sml`.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build vyperTypeDeploymentSoundnessTheory
```
(run from the project root, the directory with `holproject.toml`)

## Background

`load_contract` deploys a contract: installs initial immutables, looks up the constructor, and runs
`call_external_function` with `in_deploy = T` (defaults, argument binding, the deployment constants fold,
then lock / `send_call_value` / constructor body / return cast / unlock). This theorem is the deployment
analogue of `checked_selected_entry_no_static_error` (`vyperTypeSelectedEntrySoundnessScript.sml`): for a
contract that passes `check_contract` in both modes, a well-typed machine and context, and ABI-compatible
constructor arguments, every setup step succeeds, and the constructor run itself never raises a
TypeError and never escapes with break/continue. Genuine runtime failures are allowed.

## Domain Constraints

- Follow `AGENTS.md` at the project root. No interactive `g`/`e` sessions; probe through holbuild.
- Use holbuild only (no Holmake).
- Put helpers where they belong; don't move definitions.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Interpreter | `semantics/vyperInterpreterScript.sml` | `load_contract_def`, `call_external_function_def`, `evaluate_all_constants_def`, `initial_evaluation_context_def` |
| Checker | `semantics/type/vyperTypeContractScript.sml` | `check_contract_def`, `check_toplevel_decl_def`, `check_function_body_def` |
| Constants fold | `semantics/prop/vyperTypeConstantFoldScript.sml` | `check_contract_evaluate_all_constants` |
| Deployment machine typing | `semantics/prop/vyperTypeDeploymentMachineScript.sml` | `checked_constructor_body_setup`, `checked_constructor_body_typing_package`, `checked_constructor_body_call_evaluation_safe`, `checked_constructor_body_preserves_components`, `checked_constructor_prefix_run_preserves_machine_well_typed`, `checked_deployment_constants_establish_initial_env_immutables_consistent`, `deployment_initial_machine_well_typed`, `load_contract_establishes_machine_well_typed` (shows how readiness is discharged) |
| Runtime no-TypeError chain | `semantics/prop/vyperTypeContractSoundnessScript.sml` | `*_c53` lemmas (lock/send/unlock no TypeError and no control, return-typed), `call_external_function_exact_selected_no_type_error_c53`, `checked_explicit_external_body_no_type_error_selected`, `checked_call_external_no_loop_control`, `checked_deployment_constants_ready_from_check`, `checked_initial_immutables_constants_input_tags_agree` |
| Selected entry analogue | `semantics/prop/vyperTypeSelectedEntrySoundnessScript.sml` | `call_external_body_def`, `checked_selected_entry_no_static_error` |
| Readiness | `semantics/prop/vyperTypeEntryReadinessScript.sml` | `checked_deployment_constants_ready_def`, `checked_deployment_constants_establish_machine_well_typed`, `provided_args_typed_def` |
| Statement soundness | `semantics/prop/vyperTypeStmtSoundnessScript.sml` | `eval_stmts_no_type_error`, `eval_stmts_type_preservation_exception` |
| Eval soundness | `semantics/prop/vyperTypeEvalSoundnessScript.sml` | `stmts_no_control_escape_eval_stmts_no_loop_control` |
| Static maps | `semantics/prop/vyperTypeContractStaticMapsScript.sml` | `lookup_function_Deploy_SOME_cases` |
| Contract context | `semantics/prop/vyperTypeContractContextScript.sml` | `check_contract_deploy_function_body_MEM` |
| Built signatures | `.holbuild/` under the project root (`*.sig`) | exact theorem statements |

## Notes

- Several needed runtime lemmas are `[local]` in `vyperTypeContractSoundnessScript.sml`.
- The synthetic constructor (`lookup_function_Deploy_SOME_cases`, first disjunct) has `nr = F`, `args = []`, `body = []`.
