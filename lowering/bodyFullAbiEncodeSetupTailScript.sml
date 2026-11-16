(* Physical setup after the output allocation.  No execution is selected per horizon. *)
Theory bodyFullAbiEncodeSetupTail
Ancestors
  bodyFullAbiEncodeOffset bodyFullAbiEncodeStore bodyFullPathHistory
  bodyPtrMakeArrayPrimitiveInstall abiBuiltinEncodeCode typedMemoryCopy
  wordArgsPtr bodyFullUnwrapRun exprLoweringProps localPtrsProps bodyPtrMakeArrayWordStore exprSimPtrTopLevelImmutableCopy
  fragExec fragGasOriginPtr wordLoadStorePtr robustCopyTransportPtr
  emitHelper emitHelperProps compileEnv venomState venomExecSemantics
  instMemFrontier memSafeRun unitTransformDefs contextCodegenRel codegenRel
  words arithmetic finite_map pred_set ptrDiscipline venomInst bodyPtrDefs

Theorem setup_literal_store_origin[local]:
  emit_void MSTORE [Var dst;Lit w] a = ((),b) /\ fn_has_code a b func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var dst s = SOME (n2w p) /\ p < dimword(:256) /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\
  p+32 <= s.vs_alloca_next ==>
  ?t tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf)) /\
    t = (mstore p w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    tf = (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> mem_word_at p mem = w) /\
    (!D d ce cx es.
      ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
      lo <= p /\ (!name base sz. local_region ce es.scopes s name base sz ==>
        regions_disjoint p 32 base sz) ==>
      ghost_inv_at D lo d ce cx es G tf t) /\
    (!ce es origin G0 tn0 s0.
      ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G tf)
Proof
  strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  qexistsl_tac [`mstore p w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}`] >>
  simp[] >> conj_tac >- suspend "path" >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "inv" >>
  rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> simp[op_taint_def, SUBSET_DEF]
QED

Resume setup_literal_store_origin[path]:
  gen_tac >>
  drule_at (Pat `get_instruction _ _ = _`) abi_encode_mstore_origin_path >>
  simp[eval_operand_def, op_taint_def, w2n_n2w,
    SRULE [eval_operand_def, op_taint_def] toplevel_immutable_mstore_ghost_frame] >>
  disch_then irule >> simp[] >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    sized_source_write_range_def, eval_operand_def] >> metis_tac[]
QED

Resume setup_literal_store_origin[robust]:
  rpt strip_tac >>
  `step_taint (mk_inst a.cs_next_id MSTORE [Var dst;Lit w] []) s (mstore p w s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32})` by
    metis_tac[SRULE [eval_operand_def, op_taint_def] toplevel_immutable_mstore_ghost_frame,
      w2n_n2w, LESS_MOD] >>
  drule_at (Pat `lookup_var _ _ = _`) mstore_raw_robust_word >>
  disch_then irule >> simp[eval_operand_def, op_taint_def] >> metis_tac[w2n_n2w, LESS_MOD]
QED

Resume setup_literal_store_origin[inv]:
  rpt strip_tac >>
  `ghost_kept_at lo ce es a G tn s G tn` by simp[ghost_kept_at_refl] >>
  drule_all abi_encode_mstore_frame_at >>
  disch_then (qspecl_then [`a.cs_next_id`, `a`, `G`, `tn`, `s`] mp_tac) >>
  FAIL_TAC "store invariant"
QED

Finalise setup_literal_store_origin
