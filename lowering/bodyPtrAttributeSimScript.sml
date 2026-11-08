Theory bodyPtrAttributeSim
Ancestors
  bodyPtrAttributeSummary bodyPtrDefs exprSimAttribute exprSimSource
  exprSimHyps exprLoweringProps exprSimDefs exprSimAttributeProps
  fragGasPathPtr gasSummaryComposePtr gasExemptCert gasSummary
  exprLowering context compileEnv loweringPosts vyperState vyperAST
  exprSimUnwrap fragExec

Theorem attribute_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty obj es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >> drule attr_pre_base >> strip_tac >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >> suspend "exempt"
QED

Resume attribute_vv_sim_ptr[normal]:
  qpat_x_assum `expr_type obj = _` (SUBST_ALL_TAC o SYM) >>
  drule_all (attribute_summary_ok_ptr |> SRULE [expr_type_def, mk_ptr_def]) >>
  simp[expr_type_def, mk_ptr_def]
QED
Resume attribute_vv_sim_ptr[exception]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  `eval_expr cx (Attribute ann obj fld) = bind (eval_expr cx obj)
    (\v. select_result cx (expr_type obj) v (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >> asm_rewrite_tac[] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED
Resume attribute_vv_sim_ptr[exempt]:
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  `eval_expr cx (Attribute ann obj fld) = bind (eval_expr cx obj)
    (\v. select_result cx (expr_type obj) v (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >>
  asm_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED
Finalise attribute_vv_sim_ptr
