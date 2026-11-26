(* The zero-capacity Convert branch emits a literal, not a load. *)
Theory bodyConvertZeroCapacityMods
Ancestors
  bodySimStmtFacts bodyWriteSubscriptSourceMods exprBodyPreProps
  exprSimConvertFromBytes exprSimConvert exprLowering
  vyperTypeConversions vyperTypeEvalCaseProofs vyperTypeSystem
  vyperTypeExprSoundness vyperContext vyperTyping vyperValue
  vyperValueOperation vyperState vyperInterpreter

Theorem convert_zero_capacity_result_mods:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  valid_conversion (expr_type e) dst /\ well_formed_type env.type_defs dst /\
  (lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type ce e = BaseT (StringT 0)) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type rt v ==>
  ?vout dtv. convert_result cx (expr_type e) dst v = INL vout /\
    evaluate_type (get_tenv cx) dst = SOME dtv /\
    value_has_type dtv vout /\ typed_val_to_w256 dtv vout = 0w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by
    simp[write_subscript_source_gas_obs_mods] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  qpat_x_assum `!u. INL v = INL u ==> value_runtime_typed _ _ u`
    (qspec_then `v` mp_tac) >>
  simp[value_runtime_typed_def] >>
  disch_then (qx_choose_then `stv` strip_assume_tac) >>
  `?vout dtv. convert_result cx (expr_type e) dst v = INL vout /\
     evaluate_type (get_tenv cx) dst = SOME dtv /\
     typed_val_to_w256 dtv vout = 0w` by
    (irule dynamic_empty_scalar_convert >>
     conj_tac >- simp[] >>
     reverse conj_tac >- (qexists_tac `env.type_defs` >> simp[]) >>
     qexistsl_tac [`expr_type e`,`stv`,`v`] >> simp[] >>
     qpat_x_assum `lowered_value_type _ _ = _ \/ _` strip_assume_tac >>
     gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def]) >>
  qexistsl_tac [`vout`,`dtv`] >> simp[] >>
  irule valid_conversion_success_type >>
  qexistsl_tac [`cx`,`stv`,`expr_type e`,`dst`,`v`] >> simp[] >>
  qpat_x_assum `convert_result _ _ _ _ = _` mp_tac >>
  simp[convert_result_def, Once evaluate_type_builtin_def, AllCaseEqs()]
QED
