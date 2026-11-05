(* Memory-safe compilation of local names whose type is a word type without a
   word value (address, bytesM): the lowering loads the slot with MLOAD. *)
Theory bodyNameWordTypeMemory
Ancestors
  bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack exprSimMemoryRead fragGasSeqMem
  fragGasPathMem gasNormalPrefix gasSummary gasContext gasCount fragGasMode
  loweringPosts exprSimNameWord exprSimNameValue loweringSlice exprLowering
  exprLoweringProps fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs valueEncodingProps
  list rich_list finite_map words arithmetic

Theorem body_wordtype_name_region[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel ctx func ce cx es s ==>
  ?entry p sz w.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    local_region ce es.scopes s id (w2n w) sz /\ 32 <= sz /\
    mload (w2n w) s = typed_val_to_w256 entry.type entry.value
Proof
  rpt strip_tac >> drule_all body_name_source_region >> strip_tac >>
  drule_all word_tv_memory_size >> strip_tac >>
  drule_all val_in_memory_word_type >>
  simp[mem_word_at_eq_mload] >> strip_tac >>
  qexistsl [`entry`, `p`, `sz`, `w`] >> simp[]
QED

Theorem body_wordtype_name_MLOAD_frontier[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  inst_mem_below_frontier (mk_inst iid MLOAD [Var p] outs) s
Proof
  rpt strip_tac >> drule_all body_wordtype_name_region >> strip_tac >>
  gvs[] >> irule body_local_ptr_MLOAD_frontier >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[n2w_w2n]
QED

Theorem compile_name_wordtype_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\
    is_word_type ann /\ ~word_value_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  cheat
QED
