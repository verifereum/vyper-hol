(* Counted execution of the actual output allocation and scalar tuple encoder. *)
Theory logTuplePathPtr
Ancestors
  logTupleCallerPtr fragGasSeqPtr ghostPcTransportPtr exprLoweringProps
  exprSimPtrLiteralBuffer
  bodyPtrDefs stmtFragPtr localPtrsProps ptrDiscipline venomState compileEnv
  venomInst finite_map words list arithmetic

Theorem log_allocated_tuple_path_ptr:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand (Var src) ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srcCap) /\ srcid < st.cs_next_id /\
  inputCap <= srcCap /\ sb+srcCap < dimword (:256) /\ outcap < dimword (:256) /\
  not_fresh_at st src /\ lookup_var src s = SOME (n2w sb) /\
  ptr_covers G tn src s srcCap /\ ~ctx_has_dalloca ctx /\
  ghost_inv d ce cx es G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input ei (Tuple ats) (ListV avs) sb inputCap q) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st s /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st end_st) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?actual db H tm.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st end_st))) H tm
      (OK (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st))) /\
    run_inst_seq (emitted_insts st end_st) s = OK actual /\
    inst_extends st end_st /\
    fresh_vars_wrt limit_st
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) /\
    stmt_state_rel ctx func ce cx es
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) /\
    eval_operand dst.buf_operand
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) = SOME (n2w db) /\
    db < dimword (:256) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs)))
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)).vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) =
      SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    (!i. db <= i /\ i < db+LENGTH (enc (Tuple ats) (ListV avs)) ==> i NOTIN tm.t_mem) /\
    ghost_inv d ce cx es H tm
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) /\
    ghost_kept ce es st G tn s H tm /\
    (?dv. dst.buf_operand = Var dv /\ ptr_covers H tm dv
      (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) outcap) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op (actual with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st end_st)) = SOME w)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_allocated_tuple_sequence_ptr >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `actual` (qx_choose_then `db` (qx_choose_then `H`
      (qx_choose_then `tm` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >> disch_tac >>
  qexistsl_tac [`actual`,`db`,`H`,`tm`] >>
  asm_simp_tac bool_ss [venom_state_accfupds, eval_operand_inst_idx,
    stmt_state_rel_inst_idx, fresh_vars_wrt_def, ptr_covers_inst_idx,
    PURE_REWRITE_RULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize] >>
  qpat_x_assum `fresh_vars_wrt limit_st actual` mp_tac >>
  simp_tac bool_ss [fresh_vars_wrt_def]
QED
