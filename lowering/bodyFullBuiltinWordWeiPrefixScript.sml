(* AsWeiValue argument shape and source/lowering interfaces. *)
Theory bodyFullBuiltinWordWeiPrefix
Ancestors
  exprSimWordBuiltins exprSimWordArgs exprSimHypsDefs
  gasShadow bodyFullPreds gasOutcomeFullCompose
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
