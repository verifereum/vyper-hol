(* Type-interface probes for effect-free external-call operands. *)
Theory exprExtRequestTyping
Ancestors
  exprExtRequestBuffer supportedExprTraverse
  vyperTypeSystem exprLowering compileEnv vyperAST

Theorem extrequest_effect_free_not_call:
  !e. ~expr_has_effect e ==> !ann ct args d. e <> Call ann ct args d
Proof
  rpt strip_tac >> gvs[expr_has_effect_def] >>
  metis_tac[supported_expr_exists_root, expr_effect_root_def]
QED

Theorem extrequest_lowered_type_compatible:
  !env cenv e. well_typed_expr env e /\ ~expr_has_effect e ==>
    lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (lowered_value_type cenv e) /\
    is_bytestring_type (expr_type e)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `e` >>
  gvs[lowered_value_type_def, expr_type_def, well_typed_expr_def,
      is_bytestring_type_def]
  >- (Cases_on `t` >> Cases_on `l` >>
      gvs[lowered_value_type_def, is_bytestring_type_def, well_typed_literal_def] >>
      qmatch_goalsub_rename_tac `BaseT bt` >> Cases_on `bt` >>
      gvs[lowered_value_type_def, is_bytestring_type_def, expr_type_def] >>
      qmatch_goalsub_rename_tac `BytesT bd` >> Cases_on `bd` >>
      simp[lowered_value_type_def, is_bytestring_type_def, expr_type_def])
  >- (Cases_on `t0` >>
      gvs[lowered_value_type_def, type_builtin_result_ok_def,
          is_bytestring_type_def, expr_type_def])
  >> metis_tac[extrequest_effect_free_not_call]
QED
