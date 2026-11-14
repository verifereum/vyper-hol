(* Fixed-run length prefix, transported to every entry dead mask. *)
Theory extcallReturnDefaultLengthJoint
Ancestors
  bodyPtrIfExpBytesCounted instSeqPtrLo bodyCopyMemoryBase logBytesCodePtr
  bodyFullUnwrapRun fragGasCopyLoop bodyPtrIfExpBytesFrame
  exprSimBufferStore context emitHelperProps exprLoweringProps venomState venomInst venomExecSemantics
  finite_map list pred_set

Theorem return_default_bytestring_length_joint:
  compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME aw /\
  (!i. w2n aw <= i /\ i < w2n aw + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n aw + 32 <= s.vs_alloca_next ==>
  ?u Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tm)) /\
    eval_operand count_op u = SOME ((mload (w2n aw) s + 31w && ~31w) + 32w) /\
    op_taint tm count_op = {} /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all bodyPtrIfExpBytesCountedTheory.compile_bytestring_copy_len_seq_ptr >>
  disch_then (qspecl_then
    [`<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`,
     `func`, `PG`] strip_assume_tac) >>
  drule compile_bytestring_copy_len_code >> strip_tac >>
  drule buffer_copy_len_shape >> simp[same_blocks_def] >> strip_tac >>
  `tnf.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_frame >>
     goal_assum (drule_at Any) >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  qexistsl_tac [`sf with vs_inst_idx := LENGTH sb.cs_current_insts`, `Gf`, `tnf`] >>
  conj_tac >- suspend "path" >>
  `(~31w:bytes32) = i2w (-32)` by
    (simp[integer_wordTheory.i2w_def] >> blastLib.BBLAST_TAC) >>
  gvs[eval_operand_def, lookup_var_def, venom_state_component_equality]
QED
Resume return_default_bytestring_length_joint[path]:
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[] >>
  conj_tac >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
    strip_tac >> gvs[is_terminator_def]) >>
  conj_tac >- (irule compile_bytestring_copy_len_body_mem_ok >>
    goal_assum (drule_at (Pat `compile_bytestring_copy_len _ _ = _`)) >>
    qexists_tac `aw` >> simp[eval_operand_def]) >>
  irule inst_seq_ptr_zero_to_lo >>
  simp[] >>
  qexists_tac `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>` >>
  simp[]
QED
Finalise return_default_bytestring_length_joint
