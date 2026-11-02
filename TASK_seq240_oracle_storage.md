# TASK: Repair expression oracle-storage preservation proofs

## Meta
Status: planned
Created: 2026-11-02
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem eval_expr_oracle_storage_mutual:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx tyv id body vs. eval_for cx tyv id body vs = eval_for cx tyv id body vs) /\
  (!cx e. !env st res st'.
    runtime_storage_consistent env cx st /\ source_supply st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ int_calls_expr e = [] /\
    ~supported_expr_exists expr_evm_run_root e /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    int_calls_exprs es = [] /\ ~supported_exprs_exists expr_evm_run_root es /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\ runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
    int_calls_target bt = [] /\ ~supported_target_exists expr_evm_run_root bt /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_base_place cx bt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt. !env ty st res st'.
    well_typed_target env tgt ty /\ runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target tgt) /\
    int_calls_target tgt = [] /\ ~supported_target_exists expr_evm_run_root tgt /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_target_place cx tgt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_storage_consistent env cx st /\ source_supply st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    int_calls_exprs es = [] /\ ~supported_exprs_exists expr_evm_run_root es /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr_results cx es st = (res,st') ==> contract_storage_well_formed cx st')
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All other existing theorem statements and executable definitions are frozen.

## Completion Criteria

- Repair the failing suspended RawRevert case and any subsequent failing proof cases of the same frozen mutual theorem.
- Remove the temporary admission and build exprOracleStoragePreservationTheory.
- Preserve the existing suspension/case coverage. Retain only proof helpers consumed by this theorem.
- No new admissions, hypotheses, axioms, or executable-definition changes.
- Commit only the affected theory and this task file. Use the exact trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.
- Do not push, merge, rebase, squash, or edit unrelated files.

## Build

```sh
holbuild -j2 build exprOracleStoragePreservationTheory
```

The owner runs final CI-mode checks separately. Keep the default tactic timeout.

## Background

The theorem is being migrated to a supply-bounded runtime domain. The current build fails in the RawRevert case after the lower source/runtime/storage theories built. Repair the proof while preserving the theorem's exact domain, conclusion, and all supported cases.

## Domain Constraints

- No new axioms, oracle use, retained cheats, or timeout overrides.
- No TRY/ORELSE around proof search.
- Use holbuild, never interactive proof-state tools or Holmake.
- Preserve every existing theorem statement and executable definition.
- Existing imported admissions outside this theory are acceptable dependencies; add none.

## Available Resources

- lowering/exprOracleStoragePreservationScript.sml
- lowering/exprOracleStorageInterfacesScript.sml
- semantics/prop/vyperOracleCallStorageScript.sml
- semantics/prop/vyperTypeEvalStoragePreservationScript.sml
- semantics/prop/vyperTypeEvalSoundnessScript.sml
- semantics/prop/supply/source/vyperSourceSupplyLib.sml
- semantics/prop/supply/source/vyperSourceSupplyScript.sml
- semantics/vyperInterpreterScript.sml
- .holbuild/logs/current/vyper-hol/exprOracleStoragePreservationTheory/build.log

## Notes

The original failing RawRevert proof is preserved in a source comment. No new semantic behavior is requested. An existing local tactic adapter forwards supply facts before storage simplification and rule application. All public interfaces stay frozen.
