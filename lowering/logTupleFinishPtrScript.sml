(* The completed member layout supplies a clean numeric cursor and ABI bytes. *)
Theory logTupleFinishPtr
Ancestors
  logScalarMembersCompletePtr logInstSeqPtr logTopicScalarPtr ghostPcTransportPtr
  logMembersInvariantPtr stmtSimLogEncodeLayout stmtSimLogScalarMembers stmtFragPtr
  appendStorageGhostPtr bodyPtrDefs abiCanonicalWindows abiDecoderEffect abiDecoderFrame
  emitHelperProps exprLoweringProps compileEnv fragExec fragGasSeqPtr
  venomState venomInst venomExecSemantics instIdxIndep words list arithmetic
  valueEncoding finite_map abiEncoderMemberCode

(* Supplement the existing clean-load certificate with purely operational frames. *)
Theorem log_mload_run_frame:
  emit_op MLOAD [Var dp] st = (out,final) /\
  run_inst_seq (emitted_insts st final) s = OK t /\
  lookup_var dp s = SOME a /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
  abi_decode_footprint_frame [] s t /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `eval_operand (Var dp) s = SOME a` by simp[eval_operand_def] >>
  drule step_MLOAD >> disch_tac >>
  `t = update_var (STRING #"%" (toString st.cs_next_var)) (mload (w2n a) s) s` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, step_MLOAD, eval_operand_def]) >>
  gvs[update_var_def, abi_decode_footprint_frame_def] >>
  fs[fresh_vars_wrt_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `st.cs_next_var < n` by decide_tac >>
  `STRING #"%" (toString st.cs_next_var) <> STRING #"%" (toString n)` by
    (simp[] >> metis_tac[ASCIInumbersTheory.toString_11]) >> simp[]
QED

Theorem log_completed_layout_load_seq_ptr:
  log_members_layout [] [] [] tys avs sb so hl d hl cap s.vs_memory /\
  emit_op MLOAD [Var dp] st = (out,final) /\
  ptr_covers G tn dp s 32 /\ lookup_var dp s = SOME (n2w p) /\
  mload p s = n2w (hl+LENGTH (FLAT (abi_tuple_tails tys avs))) /\
  p < dimword(:256) /\ (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?H tm t.
    run_inst_seq (emitted_insts st final) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st final) s H tm /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) t.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ fresh_vars_wrt limit_st t /\
    abi_decode_footprint_frame [] s t /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule log_members_layout_complete >> disch_tac >>
  drule log_members_layout_final_length >> disch_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `w2n (n2w p:bytes32) = p` by simp[w2n_n2w] >>
  drule emit_mload_clean_seq_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`fn`,`ctx`,`PG`,`D`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac))) >>
  `final.cs_next_var <= limit_st.cs_next_var` by simp[] >>
  drule_all log_mload_run_frame >> strip_tac >>
  `tm.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     simp[mk_inst_def]) >>
  qexistsl_tac [`H`,`tm`,`t`] >> asm_simp_tac bool_ss [] >>
  simp[eval_operand_def] >>
  qpat_x_assum `emitted_insts st final = _` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Theorem log_scalar_members_finish_seq_ptr:
  compile_abi_encode_complex_elems (Var dst) (Var src) infos 0 0 (Var dp) st = (ignored,final) /\
  log_members_layout infos tys avs [] [] sb 0 0 d hl cap s.vs_memory /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  not_fresh_at st src /\ not_fresh_at st dst /\ not_fresh_at st dp /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  lookup_var dp s = SOME (n2w p) /\ mload p s = n2w hl /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\ ptr_covers G tn dp s 32 /\
  abi_encoder_member_span infos <= srcCap /\ sb+srcCap < dimword(:256) /\
  d+cap < dimword(:256) /\ p+32 < dimword(:256) /\
  (sb+abi_encoder_member_span infos <= d \/ d+cap <= sb) /\
  (sb+abi_encoder_member_span infos <= p \/ p+32 <= sb) /\
  (d+cap <= p \/ p+32 <= d) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ fresh_vars_wrt limit_st s /\
  emit_op MLOAD [Var dp] final = (out,end_st) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple tys) (ListV avs)) < dimword(:256) ==>
  ?H tm t.
    run_inst_seq (emitted_insts st end_st) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st end_st) s H tm /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st end_st) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) t.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    log_members_layout [] [] [] tys avs sb (abi_encoder_member_span infos) hl d hl cap t.vs_memory /\
    mload p t = n2w (hl+LENGTH (FLAT (abi_tuple_tails tys avs))) /\
    abi_decode_footprint_frame [(d,cap);(p,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!i. d <= i /\ i < d+hl ==> i NOTIN tm.t_mem) /\
    (!i. d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails tys avs)) ==> i NOTIN tm.t_mem) /\
    (!i. d <= i /\ i < d+LENGTH (enc (Tuple tys) (ListV avs)) ==> i NOTIN tm.t_mem) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tm.t_mem) /\
    (!i. ~(d <= i /\ i < d+cap) /\ ~(p <= i /\ i < p+32) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v)) /\
    lookup_var src t = SOME (n2w sb) /\ lookup_var dst t = SOME (n2w d) /\
    lookup_var dp t = SOME (n2w p) /\
    ptr_covers H tm src t srcCap /\ ptr_covers H tm dst t cap /\ ptr_covers H tm dp t 32
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `final.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_scalar_members_complete_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `J` (qx_choose_then `tk` (qx_choose_then `u` strip_assume_tac)))) >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st final)` >>
  `log_members_layout [] [] [] tys avs sb (abi_encoder_member_span infos) hl d hl cap u1.vs_memory /\
   ptr_covers J tk dp u1 32 /\ lookup_var dp u1 = SOME (n2w p) /\
   mload p u1 = n2w (hl+LENGTH (FLAT (abi_tuple_tails tys avs))) /\
   fresh_vars_wrt limit_st u1` by
    gvs[Abbr `u1`, lookup_var_def, mload_def, fresh_vars_wrt_def] >>
  `p < dimword(:256)` by decide_tac >>
  drule_all log_completed_layout_load_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "compose"
QED

Resume log_scalar_members_finish_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  `inst_extends final end_st` by (drule inst_extends_emit_op >> simp[]) >>
  `inst_extends st end_st` by
    (irule inst_extends_trans >> qexists_tac `final` >> simp[]) >>
  `emitted_insts st end_st = emitted_insts st final ++ emitted_insts final end_st` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts final end_st)` by simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq (emitted_insts st end_st) s = OK (v with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st end_st) s H tm` by
    (qunabbrev_tac `u1` >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts final end_st)` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all successful_seq_ptr_append >> asm_rewrite_tac[]) >>
  `st.cs_next_var <= final.cs_next_var` by
    (drule abi_encoder_members_bounds >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at final x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at st x ==>
    lookup_var x v = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at final x` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at final x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _` (qspec_then `x` mp_tac) >>
     simp[Abbr `u1`] >> rpt strip_tac >> gvs[lookup_var_def]) >>
  suspend "post"
QED
Resume log_scalar_members_finish_seq_ptr[post]:
  markerLib.RESUME_TAC >>
  `!x C. not_fresh_at st x /\ ptr_covers G tn x s C ==> ptr_covers H tm x v C` by
    (rpt strip_tac >> irule ptr_covers_old_transport >>
     qexistsl_tac [`G`,`s`,`st`,`tn`] >> asm_simp_tac bool_ss [] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `lookup_var src v = SOME (n2w sb) /\ lookup_var dst v = SOME (n2w d) /\
   lookup_var dp v = SOME (n2w p)` by metis_tac[] >>
  qexistsl_tac [`H`,`tm`,`v with vs_inst_idx := u.vs_inst_idx`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- gvs[fresh_vars_wrt_def] >>
  conj_tac >- (asm_rewrite_tac[] >> simp[EVERY_APPEND, mk_inst_def, is_terminator_def]) >>
  conj_tac >- simp[eval_op_inst_idx] >>
  asm_simp_tac bool_ss [] >>
  simp[Abbr `u1`, lookup_var_def, mload_def] >>
  suspend "frames"
QED
Resume log_scalar_members_finish_seq_ptr[frames]:
  markerLib.RESUME_TAC >>
  gvs[lookup_var_def, mload_def] >>
  qpat_x_assum `abi_decode_footprint_frame _ s u` mp_tac >>
  qpat_x_assum `abi_decode_footprint_frame [] _ v` mp_tac >>
  simp[abi_decode_footprint_frame_def]
QED
Finalise log_scalar_members_finish_seq_ptr
