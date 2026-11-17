(* AsWeiValue argument shape and source/lowering interfaces. *)
Theory bodyFullBuiltinWordWeiPrefix
Ancestors
  exprSimWordBuiltins exprSimWordArgs exprSimHypsDefs
  gasShadow bodyFullPreds gasOutcomeFullCompose gasShadowCompileStmtHelpers gasShadowState
  vyperTypeSystem vyperAST vyperInterpreter vyperContext vyperState list

Theorem as_wei_value_argument_shape:
  !cenv cx env ann dn args es.
    expr_body_pre cenv cx env (Builtin ann (AsWeiValue dn) args) es ==>
    ?e k. args = [e] /\ expr_type e = BaseT (UintT k) /\
          ann = BaseT (UintT 256)
Proof
  rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      LENGTH_EQ_NUM_compute, is_uint_type_def]
QED

Theorem as_wei_value_source_bind:
  !cx ann dn e.
    bind (eval_expr cx (Builtin ann (AsWeiValue dn) [e])) (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (builtin_result cx ee.accounts ann (AsWeiValue dn)
                 [expr_type e] [v], ee))
Proof
  rpt gen_tac >>
  simp[eval_expr_builtin_action, builtin_args_length_ok_def,
       eval_exprs_cons_action, Once evaluate_def, bind_assoc] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >>
  simp[FUN_EQ_THM, bind_def, return_def]
QED

Theorem as_wei_value_lower_pair:
  expr_type e = BaseT (UintT k) /\
  gas_shadow_state sa sha /\
  lower_value compile_expr cenv ty (Builtin ann (AsWeiValue dn) [e]) sa = (op,sb) /\
  lower_value compile_expr cenv ty
    (gas_shadow_expr (Builtin ann (AsWeiValue dn) [e])) sha = (op,shb) ==>
  ?x s1 sh1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) sha = (x,sh1) /\
    gas_shadow_state s1 sh1 /\
    compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) /\
    compile_as_wei_value_int x (denomination_multiplier dn) F sh1 = (op,shb)
Proof
  rpt strip_tac >>
  drule_all lower_value_as_wei_value >> strip_tac >>
  `expr_type (gas_shadow_expr e) = BaseT (UintT k)` by simp[gas_shadow_expr_type] >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
  drule_all lower_value_as_wei_value >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `expr_type e`] gas_shadow_stmt_lower_value) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`, `sha`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[] >> metis_tac[]
QED
