# TASK: Prove the external source result and body frame

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/loweringRuntimeCorrectScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem external_body_source_ok:
  !tops am tx ret vs mut args fbody env es0 res es'.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody es0 = (res, es') ==>
    stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)

Theorem external_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, F, tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings fbody /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret fbody = SOME env' /\
      EVERY (stmt_exprs_ok cenv) fbody /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts fbody)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria
- Replace both assigned cheats with kernel-checked proofs and preserve both statements byte for byte.
- Build all changed theories and loweringRuntimeCorrectTheory; record saved theorem evidence.
- No new cheats, axioms, extra hypotheses, timeout overrides, or TRY/ORELSE around search tactics.
- Keep the separate entry execution, value-revert, return-frame, RevertData and stmts_env_ret_ty obligations unchanged.
- Stop and report a concrete counterexample if a statement is false. Do not amend executable definitions or stage contracts.

## Build
```sh
holbuild -j2 build loweringRuntimeCorrectTheory
```
Default 2.5s tactic budget. Do not skip checkpoints or proof steps during proof development.

## Background
These two obligations connect selected source entry and the generated external function's compilation frame to body_stmts_sim. Their sole direct consumer is lower_vyper_runtime_unit_body in the same theory. Prove the exact current statements, preserving top-level assumptions.

## Domain Constraints
- Work only in this branch. Never push or open PRs.
- Scope edits to these two proofs, needed imports, and consumed proof helpers. Preserve other admissions and proof scripts.
- Shared compiler/environment lemmas belong in their natural existing theories.
- Do not create evaluators or duplicate arbitrary-calldata entry execution.
- This base has source transfer_value's recipient-overflow check, and no HaltException constructor. Pending source-semantics changes are outside this task.

## Available Resources
- lowering/loweringRuntimeCorrectScript.sml — frozen statements and their consumer.
- lowering/bodySimScript.sml — body_inv, locals_alloc_ok and stmt_exprs_ok.
- lowering/exprSimHypsScript.sml — exact expr_sim_inv contract.
- lowering/bodySimEntryScript.sml — external_entry_declared and ce_locals_declared_params.
- lowering/entryLocalsScript.sml — external_entry_locals (reserved pointers).
- lowering/entryStateRelScript.sml — existing external entry state relation and compile_register_positional_args_cenv / ptrs / package_external_fn_vars.
- lowering/entryDecodePlanPropsScript.sml — package_external_fn_dec_cenv_agrees and struct/environment correspondence.
- lowering/placeTypingE2EPropsScript.sml — source_typing_ok_place_type.
- lowering/allocLimitsPropsScript.sml — fn_allocs_ok_body.
- lowering/defs/compileVyperScript.sml — build_compile_env, package_external_fn and runtime producer.
- lowering/defs/moduleLoweringScript.sml — argument registration and external compilation.
- lowering/e2eDefsScript.sml — source_typing_ok, call_outcomes_ok, source_storage_ok, source_deployment_rel and initial_venom_state_rel.
- semantics/prop/vyperTypeSelectedEntrySoundnessScript.sml — checked_selected_entry_no_static_error.
- semantics/prop/vyperTypeInitialStateScript.sml — callable entry type soundness facts.
- semantics/prop/vyperTypeEvalSoundnessScript.sml — callable_body_typing_from_env_consistent, no_fallthrough_eval_no_success and control escape.
- semantics/prop/vyperTypeStmtSoundnessScript.sml — eval_stmts_no_type_error.
- semantics/prop/vyperTypeContractSoundnessScript.sml — checked-contract selected body setup and call graph safety.
- semantics/prop/vyperTypeContractFunctionScript.sml — checked_explicit_external_body_typing_package and checked_explicit_external_post_prefix_body_no_type_error_selected.
- lowering/supported/supportedProgramScript.sml — program and function body support.

## Notes
Existing out-of-scope admissions are inherited dependencies, not permission to introduce or relocate cheats.

