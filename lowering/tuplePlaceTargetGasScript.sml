(* Typed targets admit only normal places and expression-like failures. *)
Theory tuplePlaceTargetGas
Ancestors
  tuplePlaceSourceHead exprSimHypsDefs gasContext targetPlaceSimCases
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperExprNoControl
  targetPlaceSim exprSimSource supportedExprTraverse vyperTypeCallGraph

(* The static part of each index's expr_body_pre, collected over the
   target: no evm-run root and every internal call supported. *)
Theorem target_indices_pre_static[local]:
  !bt. target_indices_pre cenv cx env bt /\ expr_sim_inv cenv cx env es ==>
  ~supported_target_exists expr_evm_run_root bt /\
  EVERY (\c. FST c = NONE /\
             ?tops. supported_program tops /\
                    get_module_code cx NONE = SOME tops /\
                    IS_SOME (supported_function_decl tops c Internal))
    (int_calls_target bt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_pre_def, supported_expr_exists_def,
       int_calls_expr_def] >>
  strip_tac >> rename1 `target_indices_pre cenv cx env tgt` >>
  first_x_assum (qspec_then `tgt` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >> strip_tac >> fs[] >>
  res_tac >> fs[expr_body_pre_def, expr_has_evm_run_def]
QED

(* A target with such indices never halts: Pop evaluates exactly it first. *)
Theorem target_indices_pre_no_halt[local]:
  target_indices_pre cenv cx env bt /\ expr_sim_inv cenv cx env es ==>
  eval_target_place cx bt st <> (INR HaltException, st')
Proof
  strip_tac >> drule_all target_indices_pre_static >> strip_tac >>
  `eval_expr cx (Pop ty bt) st <> (INR HaltException, st')` by
    (irule eval_expr_calls_no_halt >>
     simp[expr_has_evm_run_def, supported_expr_exists_def,
          expr_evm_run_root_def, int_calls_expr_def]) >>
  strip_tac >> qpat_x_assum `eval_expr _ _ _ <> _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def]
QED

Theorem tuple_place_target_gas_admissible:
  expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
  well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  `env_consistent env cx (es with gas_obs := gs) /\
   state_well_typed (es with gas_obs := gs) /\
   accounts_well_typed (es with gas_obs := gs).accounts /\
   context_well_typed cx /\ functions_well_typed cx` by
    fs[expr_sim_inv_def] >>
  drule_all (cj 1 (cj 8 eval_scc_type_sound_mutual)) >> strip_tac >>
  Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `INR exc` >>
  `exc <> HaltException` by metis_tac[target_indices_pre_no_halt] >>
  drule eval_target_place_no_control >>
  Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def, target_place_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[no_type_error_result_def]
QED
