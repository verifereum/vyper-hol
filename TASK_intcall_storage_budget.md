# TASK: Bound the existing internal-call storage preservation proof

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: semantics/prop

## Theorem Statement (FROZEN)
```sml
Theorem eval_scc_storage_preservation_results_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_stmt cx s st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_stmts cx ss st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_iterator cx it st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_for cx tyv id body vs st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx e. !env st res st'.
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==> contract_storage_well_formed cx st') /\
     (!vt. type_place_expr env e = SOME vt ==>
       contract_storage_well_formed cx st'))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_base_place cx bt st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgt. !env ty st res st'.
    well_typed_target env tgt ty /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target tgt) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    eval_target_place cx tgt st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgt v. !env ty st res st'.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    assign_tuple_targets cx tgt v st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgts vs. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    protected_storage_calls_preserve cx /\
    protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\
    assign_tuple_target_list cx tgts vs st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_storage_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    protected_storage_calls_preserve cx /\ protected_storage_creates_preserve cx /\
    oracle_storage_ok cx st /\ eval_expr_results cx es st = (res,st') ==>
    contract_storage_well_formed cx st')
```
Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria
- Keep the full mutual theorem, definitions and every existing declaration statement unchanged.
- Repair the existing intcall_storage resumption at the default 2.5s step limit and build vyperTypeEvalStoragePreservationTheory.
- No admissions, axioms, new premises, feature restrictions or duplicate helpers.

## Build
holbuild -j4 build vyperTypeEvalStoragePreservationTheory

## Background
The existing intcall_storage proof exceeds the default step limit during its broad prelude simplifications. Its unchanged single reruns have failed in the same region. The task is a proof performance repair with the existing assumptions and semantics. All other proof regions remain frozen.

## Domain Constraints
Only the body of Resume eval_scc_storage_preservation_results_mutual[intcall_storage] in semantics/prop/vyperTypeEvalStoragePreservationScript.sml and consumed proof helpers immediately before that Resume may change. Search for existing helpers before adding one. Preserve every other source region and source file byte for byte. No definition or statement changes, timeout overrides, TRY/ORELSE around search or new admissions. Keep the existing proof until its replacement is checked. Do not alter independent source typing or gas simulation work.

## Available Resources
- semantics/prop/vyperTypeEvalStoragePreservationScript.sml
- semantics/prop/vyperTypeEvalSoundnessScript.sml
- semantics/vyperInterpreterScript.sml
- semantics/vyperStateScript.sml
- semantics/prop/vyperTypeInvariantsScript.sml
- semantics/prop/vyperTypeCallStackSoundnessScript.sml
- semantics/prop/vyperTypeBindArgumentsScript.sml

## Notes
The existing theorem statement already parses. This theorem has no source admissions. An independent read-only audit classified the full eleven-conjunct statement PROVABLE and checked every internal-call stage against its producers, including default evaluation, lock operations, body execution, cleanup and error outcomes. Do not run concurrently with another build in this worktree.
