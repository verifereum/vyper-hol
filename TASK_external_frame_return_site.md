# TASK: Reconcile the external body producer with return-site bounds

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
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
    call_outcomes_ok am tx vs.vs_outcomes /\
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
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
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

Do not modify this statement. Prove it as-is, or produce a counterexample.
Keep the existing external_body_source_ok statement and proof; only proof-only changes forced by actual ancestors are permitted there.

## Completion Criteria

1. loweringRuntimeCorrectTheory builds with the default proof-step budget; external_body_frame and external_body_source_ok retain proofs with no new admissions or axioms.
2. Existing substantive proof scripts are retained or repaired, never replaced by temporary admissions.
3. Owned support helpers establish the new stmt_exprs_ok conjunct from the actual lowering/package producer, with no extra public theorem assumption.

## Build

```sh
holbuild -j4 build bodySimTheory bodySimEntryTheory rawReturnHeaderTheory loweringRuntimeCorrectTheory
```

## Background

The shared return-site contract now requires return_buffer_ok at valued external nonraw returns. Its common definitions and common consumer repairs belong to a separate change. This task integrates the actual external producer with that contract. The source typing result and external-body frame target already have proofs; replay must now consume the changed contract.

## Domain Constraints

- Freeze external_body_frame and external_body_source_ok. No executable definition or source-semantics changes, no additional body_inv conjunct, no axioms or admissions, no timeout overrides, no search under TRY/ORELSE, no run/repl, and no cache/checkpoint/proof-step skips.
- Scope: stmt_exprs_ok_from_traversal_bounds, external_body_support_bounds, their external-body producer applications, and directly necessary reusable facts. Common return-site definitions and same-frame/EVERY/Return consumer repairs are owned elsewhere; do not duplicate or modify them.
- The two existing internal traversal/support helpers may gain exactly this antecedent, with their other hypotheses and conclusions retained:
  `(stmts_valued_return ss /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==> return_buffer_ok cenv)`.
- Generalize and export an existing local fact when needed; do not copy it into another theory. In particular supported_lookup_none_raw is local in rawReturnHeader and may be generalized over the return type and renamed for its general contract, updating its existing consumer.
- Preserve canonical metadata, the strict cumulative immutable guards, raw-return-aware packaging, and all inherited fixes on the merged base.
- An unchanged inherited proof-step timeout gets one retry before repair. Prefer already-checked canonical repair commits supplied by the owner. If blocked by an independently owned consumer, report the precise blocker rather than rewriting that consumer.
- Pre-existing admissions outside the requested targets are allowed dependencies; add none and do not expand scope to eliminate them.

## Available Resources

| Resource | Location | Purpose |
| --- | --- | --- |
| Frame producer and exact target | lowering/loweringRuntimeCorrectScript.sml | Existing source and external frame proofs, package metadata helpers |
| Traversal helper and body contracts | lowering/bodySimScript.sml | stmt_exprs_ok, stmt_exprs_ok_from_traversal_bounds |
| External support helper | lowering/bodySimEntryScript.sml | external_body_support_bounds |
| Lowering/package producers | lowering/defs/compileVyperScript.sml | stmt_valued_return, return_buffer_ok, external_return_buffer_ok, package_external_fn, lower_vyper_runtime_unit_return_buffer_ok |
| Raw-return lookup | lowering/rawReturnHeaderScript.sml | Existing local supported_lookup_none_raw and its consumer |
| Function classification | lowering/supported/supportedProgramPropsScript.sml | supported_external_classification, supported_external_mem |
| Parameter registration | lowering/entryStateRelScript.sml | compile_register_positional_args_cenv and declared-parameter facts |
| Valid call domain | lowering/e2eDefsScript.sml | valid_vyper_call, source_typing_ok |
| Shared posts | lowering/loweringPostsScript.sml | Extracted postconditions |

## Notes

Independent read-only statement audit found the unchanged public target PROVABLE. Preparation build parsed stmt_exprs_ok_from_traversal_bounds and reached its existing proof, which now fails with no solution at the final metis step. rawReturnHeaderTheory built, including the generalized supported_lookup_raw theorem. The amended external_body_support_bounds statement has not yet been parsed because its bodySim ancestor still needs the same migration. The unchanged public external_body_frame previously parsed and built before this return-site contract change. All existing proofs are preserved, with no temporary admission. Shared return-site definitions and common consumers are already applied from the checked dependency; do not edit them outside the two explicitly permitted producer helper statements/proofs.
