# TASK: Carry the physical supply domain through body storage preservation

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem body_oracle_storage_mutual:
  (!cx s. !tops env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    EVERY (\c. FST c = NONE) (int_calls_stmt s) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx s st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx ss. !tops env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmts_expr_exists expr_evm_run_root ss /\
    EVERY (\c. FST c = NONE) (int_calls_stmts ss) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmts cx ss st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx it. !tops env ty st res st'.
    well_typed_iterator env ty it /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_iterator_exists expr_evm_run_root it /\
    EVERY (\c. FST c = NONE) (int_calls_iterator it) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_iterator cx it st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tyv id body vs. !tops env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\ id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmts_expr_exists expr_evm_run_root body /\
    EVERY (\c. FST c = NONE) (int_calls_stmts body) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_for cx tyv id body vs st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx e. !tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!cx es. !tops env st res st'.
    well_typed_exprs env es /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_exprs_exists expr_evm_run_root es /\
    EVERY (\c. FST c = NONE) (int_calls_exprs es) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx bt. !tops env vt st res st'.
    type_place_target env bt = SOME vt /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_target_exists expr_evm_run_root bt /\
    EVERY (\c. FST c = NONE) (int_calls_target bt) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_base_place cx bt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt. !tops env ty st res st'.
    well_typed_target env tgt ty /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_target_exists expr_evm_run_root tgt /\
    EVERY (\c. FST c = NONE) (int_calls_target tgt) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target tgt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_target_place cx tgt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt v. !tops env ty st res st'.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignment_exists expr_evm_run_root tgt /\
    EVERY (\c. FST c = NONE) (int_calls_atarget tgt) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_targets cx tgt v st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgts vs. !tops env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignments_exists expr_evm_run_root tgts /\
    EVERY (\c. FST c = NONE) (int_calls_atargets tgts) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_target_list cx tgts vs st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx es. !tops env st res st'.
    well_typed_exprs env es /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_exprs_exists expr_evm_run_root es /\
    EVERY (\c. FST c = NONE) (int_calls_exprs es) /\
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr_results cx es st = (res,st') ==> contract_storage_well_formed cx st')

Theorem eval_expr_body_oracle_storage:
  !tops cx e env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    well_typed_expr env e /\
    runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res, st') ==>
    contract_storage_well_formed cx st'

Theorem eval_stmts_body_oracle_storage:
  (!tops bindings cx s env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' /\
     runtime_storage_consistent env cx st /\ source_supply st /\
     functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmt cx s st = (res, st') ==>
     contract_storage_well_formed cx st') /\
  (!tops bindings cx ss env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmts tops bindings ss /\ type_stmts env ret_ty ss = SOME env' /\
     runtime_storage_consistent env cx st /\ source_supply st /\
     functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmts cx ss st = (res, st') ==>
     contract_storage_well_formed cx st')

Theorem eval_stmts_storage_conjs:
  (!tops bindings cx s env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' /\
     runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmt cx s st = (res, st') ==>
     contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
     IS_SOME st'.outcomes) /\
  (!tops bindings cx ss env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmts tops bindings ss /\ type_stmts env ret_ty ss = SOME env' /\
     runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmts cx ss st = (res, st') ==>
     contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
     IS_SOME st'.outcomes)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
All existing expression/body simulation statements and executable definitions are frozen.
The internal helper statements in lowering/bodyStorageCasesScript.sml are weakly frozen: add source_supply on entry states and the corresponding recursive-IH states where required by this migration. Preserve every existing premise and conclusion except for the single explicitly authorized cleanup correction below. Pure frame helpers need no extra domain.

The owner authorizes correcting the false internal expansion helper body_eval_intcall_empty_defaults to match the existing evaluator exactly. Its RHS must bind rv using:
```sml
      rv <- finally_unless_halt
        (finally
          (try (do eval_stmts cxf ss; return NoneV od) handle_function)
          (pop_function prev))
        (unlock_if_nr cx nr (is_view_mut mut));
```
All other parts of that statement stay unchanged. Adapt its intcall_live consumer to this exact expansion, retaining every normal/error/halt case. The current unconditional unlock expansion has a checked reachable Halt counterexample even with source_supply. This correction changes no executable definition or frozen interface and adds no premise. Remove the diagnostic body_intcall_halt_probe from the final source once its evidence has been preserved outside the committed scripts. Resume the remaining supply migration and all five required theory builds; no human authorization is outstanding.

Independent statement audit classifies the corrected expansion PROVABLE from the evaluator and empty-defaults reduction. Its continuation reaches intcall_return and body_intcall_return_storage/body_intcall_finally_storage, which describe the old cleanup arrangement. Retain those valid standalone lemmas; add consumed local frame variants for the actual nested cleanup if needed. Those variants must preserve the same storage conclusion on every result, including Halt, and may not change executable definitions or require new assumptions on the frozen interfaces.

## Completion Criteria

The following theories build through holbuild at the default tactic timeout, with no new admissions: bodyStorageCasesTheory, bodyStoragePreservationTheory, bodySimStmtCasesTheory, exprSimHypsTheory, bodySimDeclCasesTheory.
Repair existing proofs; do not remove any case or replace an existing proof with an admission. Commit only the scoped source files and this task if updated; use trailer Bot: sol (OpenAI GPT-6.1 Sol Codex).

## Build

holbuild --max-heap 8000 -j2 build bodyStorageCasesTheory bodyStoragePreservationTheory bodySimStmtCasesTheory exprSimHypsTheory bodySimDeclCasesTheory

The prior original statement parsed and reached body_eval_expr_results_cons_storage, whose unconditional runtime subgoal now lacks source_supply. The frozen amended body mutual/wrappers have not yet been parsed; their ancestors were built. The existing proofs remain intact.

## Background

Evaluator runtime typing now uses an explicit source_supply domain. This task propagates that same domain through internal storage preservation helpers. Existing expression/body callers already carry it. No new expression/body simulation, stage or top-level assumption is permitted. The theorem conclusions and source semantics remain unchanged.

## Domain Constraints

Only edit lowering/bodyStorageCasesScript.sml, lowering/bodyStoragePreservationScript.sml, lowering/bodySimStmtCasesScript.sml, and proof blocks (only) of lowering/exprSimHypsScript.sml and lowering/bodySimDeclCasesScript.sml. New consumed local proof helpers are allowed. No axioms, cheats, tactic-timeout changes, TRY/ORELSE around search, or executable-definition changes. Do not strengthen any other theorem statement.

## Available Resources

- semantics/prop/vyperTypeEvalStoragePreservationScript.sml: existing same-domain storage preservation migration and runtime helpers.
- semantics/prop/supply/source/vyperSourceSupplyLib.sml: source supply tactic library; locate with rg --files if needed.
- semantics/prop/supply/source/vyperEvalSupplyScript.sml: evaluator supply preservation; locate with rg --files if needed.
- lowering/exprOracleStoragePreservationScript.sml and lowering/exprStoragePreservationScript.sml: migrated expression storage interfaces.
- lowering/bodySimScript.sml and lowering/bodySimMainScript.sml: existing simulation domain; statements frozen.
- lowering/exprSimHypsScript.sml: expr_body_pre_storage_preserved, existing caller supplies source_supply.
- lowering/bodySimStmtCasesScript.sml: expr_sim_inv_stmt has source_supply.
- lowering/bodySimDeclCasesScript.sml: expr_sim_inv_for_pop explicitly establishes source_supply for the pushed state.

## Notes

Preserve the complete mutual induction and all Resume labels. This is a domain propagation repair, not a new success-only typing theory. Do not push a branch or open a PR.
