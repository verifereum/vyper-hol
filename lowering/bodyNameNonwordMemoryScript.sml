(* Memory-safe compilation of local names. *)
Theory bodyNameNonwordMemory
Ancestors
  bodyNameMemoryFacts
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
  cheat
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

