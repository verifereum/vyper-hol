(* Memory case of the body induction (bodyMemory's body_mem_mutual): neg, abs
   and not on one operand, from the memory-checked unary tower
   (bodyUnopMemory). *)
Theory bodyMemBuiltinUnary
Ancestors
  bodyMemoryPreds bodyUnopMemory bodyNegMemory bodyAbsMemory bodyUnopFragMemory
  exprSimSource exprSimHypsDefs vyperTyping vyperTypeSystem vyperAST

Theorem body_builtin_unary_mem_case:
  !cx ty bt e.
    (bt = Neg \/ bt = Abs \/ bt = Not) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ty bt [e])
Proof
  rpt gen_tac >> strip_tac >>
  (match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  qpat_x_assum `body_expr_mem_ok _ _`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `!ty2. expr_sim_mem ctx func cenv cx ty2 e es` by metis_tac[] >>
  gvs[]
  >- metis_tac[compile_neg_sim_mem, compile_neg_vv_sim_mem]
  >- (`ty = BaseT (IntT 256) /\ expr_type e = BaseT (IntT 256)` by
        gvs[expr_body_pre_def, well_typed_expr_def,
            well_typed_builtin_app_def] >>
      gvs[] >> metis_tac[compile_abs_sim_mem, compile_abs_vv_sim_mem]) >>
  `ty = expr_type e /\
   (is_bool_type (expr_type e) \/ is_uint256_type (expr_type e) \/
    is_bytes32_type (expr_type e) \/ is_flag_type (expr_type e))` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> metis_tac[compile_not_sim_mem, compile_not_vv_sim_mem]
QED
