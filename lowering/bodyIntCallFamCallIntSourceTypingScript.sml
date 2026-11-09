(* Source-run typing, independent of target representation certificates. *)
Theory bodyIntCallFamCallIntSourceTyping
Ancestors
  bodyIntCallFamCallIntPureStageInterface vyperTypeEvalSoundness
  vyperTypeBindArguments exprSimAggregateChildren exprSimHypsDefs supportedExprs

Theorem intcall_source_results_runtime_typed:
  expr_sim_inv ce cx env es /\ well_typed_exprs env ds /\
  call_evaluation_safe cx (int_calls_exprs ds) /\
  eval_expr_results cx ds (es with gas_obs := gs) = (INL rs,ee) /\
  read_results cx rs ee = (INL values,ee) ==>
  exprs_runtime_typed env ds values
Proof
  strip_tac >>
  `expr_sim_inv ce cx env (es with gas_obs := gs)` by simp[] >>
  drule_at (Pos last) (cj 1 (cj 11 eval_scc_type_sound_results_mutual)) >>
  disch_then (qspec_then `env` mp_tac) >>
  impl_tac >- fs[expr_sim_inv_def] >>
  simp[] >> strip_tac >>
  drule_all read_results_typed >> simp[]
QED

Theorem intcall_pure_source_stage_facts:
  supported_pure_exprs tops ds /\
  (!e. MEM e ds ==> expr_body_pre ce cx env e es) /\
  expr_sim_inv ce cx env es /\ well_typed_exprs env ds /\
  call_evaluation_safe cx (int_calls_exprs ds) /\
  eval_expr_results cx ds (es with gas_obs := gs) = (INL rs,ee) /\
  read_results cx rs ee = (INL values,ee) ==>
  LENGTH values = LENGTH ds /\
  (!i. i < LENGTH ds ==>
    ?tv. post_value_type ce (EL i ds) = expr_type (EL i ds) /\
      evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME tv /\
      type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\
      value_has_type tv (EL i values) /\ val_wf tv (EL i values))
Proof
  strip_tac >> drule_all intcall_source_results_runtime_typed >>
  disch_then (mp_tac o MATCH_MP exprs_runtime_typed_value_expr_LIST_REL) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `MEM (EL i ds) ds` by simp[listTheory.EL_MEM] >>
  `supported_pure_expr tops (EL i ds)` by
    fs[supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  `expr_body_pre ce cx env (EL i ds) es` by metis_tac[] >>
  drule_all intcall_pure_stage_layout >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  gvs[cj 1 typed_value_wf]
QED
