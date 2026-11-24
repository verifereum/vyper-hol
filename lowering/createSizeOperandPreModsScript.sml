Theory createSizeOperandPreMods
Ancestors
  createSizeOperandPre createExprSizeExitDefsMods
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimSource allocLimits
  supportedExprTraverse vyperAST vyperTypeSystem vyperTypeCallGraph
  vyperTypeEvalProofs vyperTypeCallStackSoundness list

Theorem create_call_operand_body_pre_mods:
  expr_body_pre_mods mods ce cx env (Call ann target args df) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env ee ==>
  expr_body_pre_mods mods ce cx env e ee
Proof
  simp[expr_body_pre_mods_def] >> strip_tac >>
  `well_typed_exprs env args` by
    (qpat_x_assum `well_typed_expr _ (Call _ _ _ _)` mp_tac >>
     Cases_on `target`
     >- (rename1 `IntCall nsid` >> PairCases_on `nsid` >>
         simp[Once well_typed_expr_def])
     >- (rename1 `ExtCall static skip sg opts` >> PairCases_on `sg` >>
         simp[Once well_typed_expr_def]) >>
     simp[Once well_typed_expr_def]) >>
  `!callee. MEM callee (int_calls_exprs args) ==>
            MEM callee (int_calls_expr (Call ann target args df))` by
    (Cases_on `target` >> simp[int_calls_expr_def]) >>
  `call_evaluation_safe cx (int_calls_exprs args)` by
    (irule call_evaluation_safe_mono >> metis_tac[]) >>
  `EVERY (source_body_call_supported cx) (int_calls_exprs args)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `!P. supported_expr_exists P e ==>
       supported_expr_exists P (Call ann target args df)` by
    (simp[supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  fs[byte_widths_expr_def, alloc_limits_expr_def, expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem, alloc_limits_exprs_mem,
    int_calls_exprs_every_mem, call_evaluation_safe_exprs_mem]
QED
