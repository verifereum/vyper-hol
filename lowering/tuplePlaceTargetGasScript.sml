(* Typed targets admit only normal places and expression-like failures. *)
Theory tuplePlaceTargetGas
Ancestors
  tuplePlaceSourceHead exprSimHypsDefs gasContext targetPlaceSimCases
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperExprNoControl
  targetPlaceSim exprSimSource supportedExprTraverse vyperTypeCallGraph

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
  drule eval_target_place_no_control >>
  Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def, target_place_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[no_type_error_result_def]
QED
