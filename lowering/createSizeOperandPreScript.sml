Theory createSizeOperandPre
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimSource allocLimits
  supportedExprTraverse vyperAST vyperTypeSystem vyperTypeCallGraph
  vyperTypeEvalProofs vyperTypeCallStackSoundness list

Theorem create_call_operand_body_pre:
  expr_body_pre ce cx env (Call ann target args df) es /\
  MEM e args /\ expr_sim_inv ce cx env ee ==>
  expr_body_pre ce cx env e ee
Proof
  strip_tac >>
  fs[expr_body_pre_split_def, expr_body_pre_mods_def, byte_widths_expr_def,
     alloc_limits_expr_def, supported_expr_exists_def, supported_exprs_exists_every,
     expr_has_evm_run_thm, EXISTS_MEM] >>
  `well_typed_exprs env args` by
    (qpat_x_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     Cases_on `target`
     >- (rename1 `IntCall nsid` >> PairCases_on `nsid` >>
         simp[Once well_typed_expr_def])
     >- (rename1 `ExtCall static skip sg opts` >> PairCases_on `sg` >>
         simp[Once well_typed_expr_def]) >>
     simp[Once well_typed_expr_def]) >>
  `!P. EVERY P (int_calls_expr (Call ann target args df)) ==>
       EVERY P (int_calls_expr e)` by
    (Cases_on `target` >> simp[int_calls_expr_def, EVERY_APPEND] >>
     metis_tac[int_calls_exprs_every_mem]) >>
  `call_evaluation_safe cx (int_calls_exprs args)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr (Call ann target args df)` >>
     Cases_on `target` >> fs[int_calls_expr_def]) >>
  qpat_assum `!P. EVERY P _ ==> _` imp_res_tac >>
  simp[] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem, alloc_limits_exprs_mem,
    call_evaluation_safe_exprs_mem, expr_sim_inv_split_def]
QED
