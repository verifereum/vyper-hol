(* Memory-safe compilation of local names. *)
Theory bodyNameNonwordMemory
Ancestors
  bodyNameMemoryFacts exprSimMemDefs
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack fragGasSeqMem fragGasPathMem
  gasNormalPrefix gasSummary gasContext gasCount fragGasMode loweringPosts
  exprSimNameWord exprSimNameValue loweringSlice exprLowering exprLoweringProps
  fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs
  list rich_list finite_map words arithmetic

Theorem compile_name_nonword_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\ ~is_word_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_values >> rpt gen_tac >> strip_tac >>
  drule_all body_name_source_region >> strip_tac >>
  `ce.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >>
  gvs[lower_value_def, comp_bind_def, comp_return_def,
      unwrap_value_def, contextTheory.mk_ptr_def] >>
  `stmt_state_rel ctx func ce cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  qexistsl_tac [`[]`, `entry.value`, `es`, `s0`] >>
  reverse conj_tac
  >- (simp[expr_store_bound_def, vyperASTTheory.expr_type_def,
           eval_operand_def] >>
      rpt strip_tac >> gvs[] >> drule val_store_size_le >> decide_tac) >>
  simp[gas_value_prefix_def, gas_marked_exec_def, gas_explicit_def,
       gas_marked_path_def, gas_path_mem_rules,
       lower_value_def, comp_bind_def, comp_return_def,
       unwrap_value_def, contextTheory.mk_ptr_def] >>
  conj_tac
  >- (gen_tac >>
      qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
        mp_tac eval_name_word >> simp[vyperStateTheory.bind_def]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, locals_kept_refl] >>
  rpt strip_tac >> gvs[] >>
  disj2_tac >> disj1_tac >> qexistsl [`id`, `w2n w`, `sz`] >>
  drule val_footprint_le >> strip_tac >>
  `val_footprint entry.type entry.value <= sz` by decide_tac >> simp[] >>
  irule local_path_at_val_at >> irule local_path_at_root >> simp[]
QED

(* Prior ordinary proof, retained verbatim for reference.
Proof
  rpt strip_tac >> simp[expr_sim_mem_def] >> rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> metis_tac[]) >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >> gvs[] >>
  gvs[lower_value_def, compile_expr_def, compile_name_vv_def,
      comp_bind_def, comp_return_def, unwrap_value_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule frag_exec_mem_refl >> rpt strip_tac >> gvs[] >>
  drule_all body_name_source_region >> strip_tac >> gvs[] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, locals_kept_refl] >>
  `ce.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  disj2_tac >> disj1_tac >> qexistsl [`id`, `w2n w`, `sz`] >>
  simp[dynarray_local_def] >> drule val_footprint_le >> decide_tac
QED
*)

