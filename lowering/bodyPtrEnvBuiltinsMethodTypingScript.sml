(* Typed operand facts exposed at the marked forced-read boundary. *)
Theory bodyPtrEnvBuiltinsMethodTyping
Ancestors exprSimHash exprSimSource exprSimHypsDefs exprSimHyps exprSimProps
  exprSimWordArgs gasSummaryComposePtr gasSummary fragGasPath fragGasMode
  bodyPtrDefs vyperTypeSystem vyperValue vyperAST vyperContext
  vyperInterpreter vyperState finite_map list

Theorem method_id_operand_pre:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es ==>
  expr_body_pre cenv cx env e es /\ is_bytes_or_string_type (expr_type e) /\
  ?bty. expr_type e = BaseT bty /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `is_bytes_or_string_type (expr_type e)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  simp[] >> Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def] >>
  drule expr_body_pre_type_evaluates >>
  Cases_on `b` >> simp[evaluate_type_def] >>
  Cases_on `b'` >> simp[evaluate_type_def]
QED

Theorem method_id_marked_operand_facts:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bty /\
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INL v) ee G tn (OK t) ==>
  value_has_type (BaseTV bty) v /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ ~t.vs_halted
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,fn) (bind (eval_expr cx e) (read_result cx))
     (es,s0) marks (INL v) ee (OK t)` by
    metis_tac[gas_marked_exec_ptr_exec] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (gvs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >> strip_tac >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >>
  simp[] >> strip_tac >>
  simp[] >> metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal]
QED
