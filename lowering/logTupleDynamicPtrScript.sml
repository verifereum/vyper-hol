(* Dynamic scalar tuple encoding: compose actual cursor entry and finished members. *)
Theory logTupleDynamicPtr
Ancestors
  logTupleShapePtr logTupleEntryPtr logTupleFinishPtr logCursorAllocPtr logInstSeqPtr logDataAllocPtr
  abiBuiltinAllocation abiDecoderFrame abiEncoderComplexCode abiEncoderComplexPrefix
  abiDecoderArrayHeader valueEncodingProps abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs context fragExec fragGasSeqPtr
  venomExecSemantics venomState venomInst words list arithmetic finite_map pred_set
  stmtFragPtr instIdxIndep

(* The allocation ownership certificate frames non-memory observations; the
   literal initialization adds only the cursor cell to the memory footprint. *)
Theorem log_cursor_prefix_effect_frame:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit w] sm = ((),sb) /\
  run_inst_seq (emitted_insts sa sm) s = OK u /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
  lookup_var dp u = SOME (n2w p) /\ buf.buf_operand = Var dp /\
  p < dimword(:256) /\
  abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id 32 s u ==>
  lookup_var dp t = SOME (n2w p) /\ t.vs_allocas = u.vs_allocas /\
  abi_decode_footprint_frame [(p,32)] s t /\
  t.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
  t.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ u = OK t` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       eval_operand_def] >> strip_tac >>
  `abi_decode_frame p 32 u (mstore p w u)` by irule abi_decode_mstore_frame >>
  gvs[abi_builtin_allocation_frame_def, abi_decode_frame_def,
      abi_decode_footprint_frame_def, abi_footprint_disjoint_def, mstore_def] >>
  conj_tac >- gvs[lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem compile_log_dynamic_tuple_seq_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiComplex infos) st = (out,end_st) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  fn_has_code st end_st func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\ srcid <> st.cs_next_id /\ dstid <> st.cs_next_id /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srcCap) /\
  FLOOKUP s.vs_allocas dstid = SOME (d,cap) /\
  not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\
  sb+srcCap < dimword(:256) /\ d+cap < dimword(:256) /\
  (sb+srcCap <= d \/ d+cap <= sb) /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  abi_encoder_member_span infos <= srcCap /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= cap ==>
  ?H tm t p.
    run_inst_seq (emitted_insts st end_st) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st end_st) s H tm /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st end_st) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) t.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    (!i. d <= i /\ i < d+LENGTH (enc (Tuple tys) (ListV avs)) ==> i NOTIN tm.t_mem) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tm.t_mem) /\
    abi_decode_footprint_frame [(d,cap);(p,32)] s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\ p+32 < dimword(:256) /\
    t.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas /\
    t.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 s).vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (sb+srcCap <= p \/ p+32 <= sb) /\ (d+cap <= p \/ p+32 <= d) /\
    (!i. ~(d <= i /\ i < d+cap) /\ ~(p <= i /\ i < p+32) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_tuple_dynamic_phases >> strip_tac >>
  `abi_encode_complex_prefix infos st = (cb.buf_operand,b)` by
    simp[abi_encode_complex_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  drule_all log_tuple_dynamic_code >> strip_tac >>
  drule_all log_tuple_dynamic_prefix_code >> strip_tac >>
  mp_tac (Q.INST [`sa` |-> `st`, `sm` |-> `a`, `final` |-> `b`,
    `buf` |-> `cb`, `hl` |-> `SUM (MAP (\(_,asz,_,_). asz) infos)`]
    (SPEC_ALL log_tuple_cursor_entry)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `p` (qx_choose_then `J`
    (qx_choose_then `tk` (qx_choose_then `dp1`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `dp1 = dp` by metis_tac[operand_11] >>
  qpat_x_assum `dp1 = dp` SUBST_ALL_TAC >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx +
    LENGTH (emitted_insts st a ++ emitted_insts a b)` >>
  `LENGTH (enc (Tuple tys) (ListV avs)) < dimword(:256)` by
    (qpat_x_assum `LENGTH _ <= cap` mp_tac >>
     qpat_x_assum `d+cap < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  suspend "members"
QED

Resume compile_log_dynamic_tuple_seq_ptr[members]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`st` |-> `b`, `final` |-> `c`, `s` |-> `u1`,
    `G` |-> `J`, `tn` |-> `tk`, `fn` |-> `func`,
    `hl` |-> `SUM (MAP (\(_,asz,_,_). asz) infos)`]
    (SPEC_ALL log_scalar_members_finish_seq_ptr)) >>
  impl_tac >-
    (asm_rewrite_tac[] >>
     gvs[Abbr `u1`, lookup_var_def, mload_def, fresh_vars_wrt_def]) >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `v`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  suspend "compose"
QED

Resume compile_log_dynamic_tuple_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  `emitted_insts st b = emitted_insts st a ++ emitted_insts a b` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts st end_st = (emitted_insts st a ++ emitted_insts a b) ++
    emitted_insts b end_st` by
    (irule EQ_TRANS >> qexists_tac `emitted_insts st b ++ emitted_insts b end_st` >>
     conj_tac >- (irule emitted_insts_append >> fs[inst_extends_def]) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b end_st)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st a ++ emitted_insts a b)` by
    (qpat_x_assum `EVERY _ (emitted_insts st end_st)` mp_tac >>
     asm_rewrite_tac[EVERY_APPEND] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK (v with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st end_st) s H tm` by
    (qunabbrev_tac `u1` >> drule_all successful_seq_ptr_append >> asm_rewrite_tac[]) >>
  suspend "prefix"
QED

Resume compile_log_dynamic_tuple_seq_ptr[prefix]:
  markerLib.RESUME_TAC >>
  `32 < dimword(:256)` by simp[dimword_def] >>
  drule_all log_buffer_seq_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `w` (qx_choose_then `pa` (qx_choose_then `Ja`
      (qx_choose_then `ta` (qx_choose_then `da`
        (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))) >>
  `da = dp` by metis_tac[operand_11] >>
  qpat_x_assum `da = dp` SUBST_ALL_TAC >>
  `lookup_var dp w = SOME (n2w pa)` by
    (qpat_x_assum `eval_operand cb.buf_operand w = _` mp_tac >>
     simp[eval_operand_def]) >>
  `pa < dimword(:256)` by
    (qpat_x_assum `pa+32 < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  drule_all log_cursor_prefix_effect_frame >> strip_tac >>
  `p < dimword(:256)` by
    (qpat_x_assum `p+32 < dimword(:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `n2w p = (n2w pa:bytes32)` by metis_tac[optionTheory.SOME_11] >>
  `p = pa` by
    (qpat_x_assum `n2w p = (n2w pa:bytes32)` mp_tac >>
     asm_simp_tac bool_ss [n2w_11, LESS_MOD]) >>
  qpat_x_assum `p = pa` (SUBST_ALL_TAC o SYM) >>
  `FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,32)` by metis_tac[] >>
  `FLOOKUP w.vs_allocas srcid = SOME (sb,srcCap) /\
   FLOOKUP w.vs_allocas dstid = SOME (d,cap)` by
    metis_tac[abi_builtin_allocation_frame_outside] >>
  qpat_assum `!id b sz. _` (qspecl_then [`srcid`,`sb`,`srcCap`] mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  suspend "post"
QED

Resume compile_log_dynamic_tuple_seq_ptr[post]:
  markerLib.RESUME_TAC >>
  `st.cs_next_var <= b.cs_next_var` by
    (qpat_x_assum `a.cs_next_var = _` mp_tac >>
     qpat_x_assum `b.cs_next_var = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!x. not_fresh_at st x ==> not_fresh_at b x` by
    (qpat_x_assum `st.cs_next_var <= b.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `!x. not_fresh_at st x ==>
    lookup_var x v = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at b x` by metis_tac[] >>
     qpat_x_assum `!v. not_fresh_at b v ==> _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >>
     simp[Abbr `u1`, lookup_var_def]) >>
  qexistsl_tac [`H`,`tm`,`v with vs_inst_idx := u.vs_inst_idx`,`p`] >>
  asm_simp_tac bool_ss [] >>
  simp[eval_op_inst_idx, Abbr `u1`] >>
  suspend "frames"
QED

Resume compile_log_dynamic_tuple_seq_ptr[frames]:
  markerLib.RESUME_TAC >>
  gns[lookup_var_def, fresh_vars_wrt_def] >>
  qpat_x_assum `abi_decode_footprint_frame [(p,32)] s u` mp_tac >>
  qpat_x_assum `abi_decode_footprint_frame [(d,cap);(p,32)] _ v` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  metis_tac[]
QED
Finalise compile_log_dynamic_tuple_seq_ptr
