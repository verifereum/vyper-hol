(* Memory-safe compilation of local names. *)
Theory bodyNameValueMemory
Ancestors
  bodyNameMemoryFacts exprSimMemDefs gasOutcome
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack fragGasSeqMem fragGasPathMem
  gasNormalPrefix gasSummary gasContext gasCount fragGasMode loweringPosts
  exprSimNameWord exprSimNameValue loweringSlice exprLowering exprLoweringProps
  fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv loweringStateRelDefs context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs
  list rich_list finite_map words arithmetic

(* Historical proof, unbuilt against the counted schema; preserved verbatim.
Theorem compile_name_body_vv_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es ==>
    expr_vv_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  rpt strip_tac >> simp[expr_vv_sim_mem_def] >> rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> metis_tac[]) >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `ce.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def,
       read_result_def] >> strip_tac >>
  gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule frag_exec_mem_refl >> rpt strip_tac >> gvs[] >>
  drule_all body_name_source_region >> strip_tac >> gvs[] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def,
       vyperASTTheory.expr_type_def, eval_operand_def] >>
  rpt conj_tac
  >- metis_tac[val_in_memory_word_type]
  >- (disj2_tac >> disj1_tac >>
      qexistsl [`id`, `w2n w`, `sz`] >>
      asm_simp_tac (srw_ss()) [local_region_def] >>
      drule val_footprint_le >> strip_tac >>
      conj_tac >- decide_tac >>
      irule local_path_at_val_at >> irule local_path_at_root >> simp[]) >>
  rpt strip_tac >> gvs[]
QED
*)

Theorem compile_name_body_vv_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es ==>
    expr_vv_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  rpt strip_tac >> simp[expr_vv_sim_mem_def] >> rpt strip_tac >>
  drule_all body_name_source_region >> strip_tac >>
  `ce.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules,
          Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def] >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule name_value_post >> simp[]) >>
  simp[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def] >>
  irule name_vv_store_bound >> simp[] >> qexists_tac `sz` >> simp[]
QED

