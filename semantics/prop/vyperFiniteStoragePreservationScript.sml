(* Storage preservation over a fixed finite horizon of actual observations. *)
Theory vyperFiniteStoragePreservation
Ancestors
  vyperStorageFootprint vyperStorageTrace vyperTypeEvalStoragePreservation
  vyperTypeEvalSoundness vyperTypeSystem vyperTypeExprSoundness
  vyperTypeCallGraph vyperInterpreter vyperState vyperValue
Libs
  wordsLib

(* The horizon may contain a larger selected execution's roots. Its public
   caller supplies the horizon of that exact execution, including failures. *)
Theorem eval_storage_well_formed_on_mutual:
  !H.
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_stmt cx s st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_stmts cx ss st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_iterator cx it st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_for cx tyv id body vs st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx e. !env st res st'.
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==> storage_well_formed_on cx st' (FST H)) /\
     (!vt. type_place_expr env e = SOME vt ==>
       storage_well_formed_on cx st' (FST H)))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_exprs cx es st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_base_place cx bt st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tgt. !env ty st res st'.
    well_typed_target env tgt ty /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target tgt) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_target_place cx tgt st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tgt v. !env ty st res st'.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    storage_observations_ok cx H st'.storage_trace /\
    assign_tuple_targets cx tgt v st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tgts vs. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    storage_observations_ok cx H st'.storage_trace /\
    assign_tuple_target_list cx tgts vs st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    storage_observations_ok cx H st'.storage_trace /\ eval_expr_results cx es st = (res,st') ==>
    storage_well_formed_on cx st' (FST H))
Proof
  gen_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rw[]
QED
