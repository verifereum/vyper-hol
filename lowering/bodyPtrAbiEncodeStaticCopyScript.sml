(* Static fixed-copy child: address preparation and the framed MCOPY path. *)
Theory bodyPtrAbiEncodeStaticCopy
Ancestors
  bodyPtrAbiEncodeStaticChild bodyPtrAbiEncodeFrames bodyPtrAbiEncodeOffset
  abiEncoderChildCode abiEncoderLeafCode abiEncoderLeaves abiEncoderReentryLeaves abiEncoder
  abiDecoderContract abiDecoderReentry emitHelperProps exprLoweringProps
  compileEnv emitHelper fragGasSeqPtr fragGasPathPtr bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst
  finite_map words list rich_list arithmetic pred_set

Theorem abi_encode_static_copy_child_code:
  compile_abi_encode_child dst src (AbiCopy sz) F off cursor st = (out,en) ==>
  ?head mid.
    emit_op ADD [dst; Lit (n2w off)] st = (head,mid) /\
    compile_abi_encode_to_buf head src (AbiCopy sz) mid = (out,en) /\
    emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en /\
    LENGTH (emitted_insts st mid) = 1 /\
    LENGTH (emitted_insts mid en) = 1 /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts mid en) = [] /\
    mid.cs_next_var = st.cs_next_var+1 /\ en.cs_next_var = mid.cs_next_var
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encode_copy_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem abi_encode_static_copy_address_frame[local]:
  emit_op ADD [Var dst; Lit (n2w off)] st = (head,mid) /\
  lookup_var dst s = SOME a /\
  run_inst_seq (emitted_insts st mid) s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def, update_var_def]
QED

Theorem abi_encode_static_copy_child_checked_ptr_path:
  !total.
  compile_abi_encode_child (Var dst) (Var src) (AbiCopy sz) F off cursor st = (out,en) /\
  not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w db) /\
  sb < dimword(:256) /\ db+off < dimword(:256) /\ sz < dimword(:256) /\
  ptr_covers G tn dst s total /\ op_taint tn (Var src) = {} /\
  (0 < sz ==> ptr_covers G tn src s sz) /\
  off < total /\ off+sz <= total /\
  (!i. sb <= i /\ i < sb+sz ==> i NOTIN tn.t_mem) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st en))) /\
    eval_operand out t = SOME (n2w sz) /\
    mem_bytes_at (db+off) sz t.vs_memory = mem_bytes_at sb sz s.vs_memory /\
    fresh_vars_wrt limit_st t /\
    tnf.t_mem = tn.t_mem DIFF {i | db+off <= i /\ i < db+off+sz} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at st p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    abi_decode_frame (db+off) sz s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  gen_tac >> strip_tac >> drule abi_encode_static_copy_child_code >> strip_tac >>
  `isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+1) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >> drule abi_encode_static_child_sites >> simp[]) >>
  `w2n (n2w db:bytes32)+off < dimword(:256)` by
    (simp[w2n_n2w] >> `db < dimword(:256)` by decide_tac >> simp[]) >>
  drule_all abi_encode_offset_checked_ptr_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  suspend "after_offset"
QED

Resume abi_encode_static_copy_child_checked_ptr_path[after_offset]:
  gvs[] >>
  drule_all abi_encode_static_child_address_control >> strip_tac >>
  drule_all abi_encode_static_copy_address_frame >> strip_tac >>
  `fresh_vars_wrt limit_st t` by
    (irule abi_encode_offset_fresh_vars >> goal_assum $ drule_at Any >>
     simp[] >> goal_assum $ drule_at Any >> simp[]) >>
  `lookup_var src t = SOME (n2w sb) /\ op_taint tnf (Var src) = {}` by
    (first_assum (qspec_then `src` mp_tac) >> simp[]) >>
  `(0 < sz ==> ptr_covers Gf tnf src t sz)` by
    (strip_tac >> first_assum (qspec_then `src` mp_tac) >>
     simp[] >> gvs[ptr_covers_def, w2n_n2w]) >>
  `eval_operand (Var src) (t with vs_inst_idx := s.vs_inst_idx+1) = SOME (n2w sb) /\
   eval_operand (Var p) (t with vs_inst_idx := s.vs_inst_idx+1) = SOME (n2w (db+off))` by
    fs[eval_operand_def, lookup_var_def] >>
  `fresh_vars_wrt limit_st (t with vs_inst_idx := s.vs_inst_idx+1) /\
   lookup_block (t with vs_inst_idx := s.vs_inst_idx+1).vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts mid en)
     (DROP (t with vs_inst_idx := s.vs_inst_idx+1).vs_inst_idx bb.bb_instructions) /\
   (0 < sz ==> ptr_covers Gf tnf src (t with vs_inst_idx := s.vs_inst_idx+1) sz /\
     ptr_covers Gf tnf p (t with vs_inst_idx := s.vs_inst_idx+1) sz) /\
   ~(t with vs_inst_idx := s.vs_inst_idx+1).vs_halted` by
    fs[fresh_vars_wrt_def] >>
  drule_all abi_encode_copy_checked_ptr_path_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume abi_encode_static_copy_child_checked_ptr_path[compose]:
  gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `!i. i < sz ==> i+sb NOTIN tn.t_mem` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!i. sb <= i /\ _ ==> _` (qspec_then `i+sb` mp_tac) >> simp[]) >>
  `{db+(i+off) | i < sz /\ i+sb IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf'`, `t' with vs_inst_idx := s.vs_inst_idx`] >>
  fs[fresh_vars_wrt_def] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!q. not_fresh_at st q ==> _` drule >> simp[op_taint_def]) >>
  conj_tac >- (gvs[abi_decode_frame_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `eval_operand op t = SOME w` by
    (Cases_on `op` >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, not_fresh_at_def] >> metis_tac[]) >>
  fs[eval_operand_def, lookup_var_def]
QED
Finalise abi_encode_static_copy_child_checked_ptr_path
