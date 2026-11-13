(* Semantic facts at the actual successful tuple target endpoint. *)
Theory assignTupleTargetSourcePtr
Ancestors
  bodySimAugPlaceLoad exprSimPopNestedLocalSource exprSimHypsDefs
  vyperStoragePlaceProvenance vyperPlaceResultTyping vyperTargetPlaceWrite
  vyperTypeInvariants vyperTypeEnv vyperState

Theorem tuple_scalar_target_source_facts:
  expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
  well_typed_target env bt dty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt (es with gas_obs := obs) = (INL p,ee) /\
  evaluate_type (get_tenv cx) dty = SOME dtv ==>
  expr_sim_inv cenv cx env ee /\ runtime_place_typed cx ee p dtv /\
  runtime_place_writable cx ee p /\ storage_place_region cx p
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env (es with gas_obs := obs)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (irule aug_place_target_inv >> metis_tac[]) >>
  qpat_assum `expr_sim_inv _ _ _ (es with gas_obs := obs)`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all eval_target_place_runtime_facts >> strip_tac >>
  drule_all eval_target_place_writable >> strip_tac >>
  `runtime_place_typed cx ee p dtv` by
    gvs[eval_result_typed_def, env_consistent_def, env_context_consistent_def] >>
  `runtime_place_writable cx ee p` by fs[writable_place_result_def] >>
  asm_rewrite_tac[] >> irule eval_target_place_region >> metis_tac[]
QED
