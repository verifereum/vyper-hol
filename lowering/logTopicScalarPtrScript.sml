(* Scalar topic interface: keep raw instruction checks behind a sequence boundary. *)
Theory logTopicScalarPtr
Ancestors
  logTopicFramePtr logTopicPtr stmtSimLogTopics fragGasSeqPtr ptrDiscipline
  context compileEnv venomState words finite_map list rich_list
  emitHelper contextCodegenRel venomInst exprLoweringProps bodyPtrDefs valueEncoding arithmetic

Theorem inst_seq_ptr_immutable_taint_frame:
  !code G tn s Gf tnf.
    EVERY (\i. i.inst_opcode <> ISTORE) code /\
    inst_seq_ptr D lo ctx func PG G tn code s Gf tnf ==>
    tnf.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  gvs[inst_seq_ptr_def] >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum drule >> simp[step_taint_def, imm_taint_def]
QED

Theorem compile_encode_log_topic_immutable_taint_frame:
  compile_encode_log_topic x flag sa = (out,sb) /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf ==>
  tnf.t_imm = tn.t_imm
Proof
  strip_tac >> irule inst_seq_ptr_immutable_taint_frame >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `compile_encode_log_topic _ _ _ = _` mp_tac >>
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem compile_encode_log_topic_scalar_seq_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sm es s (x,ty) v /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sb) /\
  ptr_val_ok cx ty v x G tn s /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tnf topic.
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) s Gf tnf /\
    encode_event_topic ty v = SOME topic /\ eval_operand op t = SOME topic /\
    op_taint tnf op = {} /\ (t with vs_vars := s.vs_vars) = s /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all compile_encode_log_topic_scalar_run >> strip_tac >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes" >>
  suspend "word"
QED
Resume compile_encode_log_topic_scalar_seq_ptr[bytes]:
  drule_all log_bytestring_arg_view_ptr >> strip_tac >> gvs[] >>
  `lookup_var src s = SOME (n2w b)` by gvs[eval_operand_def] >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  `mload (w2n (n2w b : bytes32)) s = n2w (LENGTH bs)` by gvs[mload_def, mem_word_at_def] >>
  drule (Q.INST [`a` |-> `n2w b`, `bs` |-> `bs`]
    compile_encode_log_topic_bytes_seq_ptr) >>
  disch_then (drule_at Any) >>
  disch_then (drule_at Any) >>
  simp[ADD_COMM] >> strip_tac >>
  gvs[] >> first_x_assum drule_all >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `tnf.t_imm = tn.t_imm` by
    (drule_all compile_encode_log_topic_immutable_taint_frame >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[]
QED
Resume compile_encode_log_topic_scalar_seq_ptr[word]:
  gvs[compile_encode_log_topic_def, comp_return_def, emitted_insts_def,
      inst_seq_ptr_def, ptr_val_ok_def]
QED
Finalise compile_encode_log_topic_scalar_seq_ptr

Theorem compile_encode_log_topic_scalar_seq_ptr_ghost:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sm es s (x,ty) v /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sb) /\
  ptr_val_ok cx ty v x G tn s /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ghost_kept cenv es sa0 G0 tn0 s0 G tn /\ sa0.cs_next_var <= sm.cs_next_var ==>
  ?t Gf tnf topic.
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) s Gf tnf /\
    encode_event_topic ty v = SOME topic /\ eval_operand op t = SOME topic /\
    op_taint tnf op = {} /\ (t with vs_vars := s.vs_vars) = s /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ghost_inv d cenv cx es Gf tnf t /\
    ghost_kept cenv es sa0 G0 tn0 s0 Gf tnf
Proof
  strip_tac >> drule_all compile_encode_log_topic_scalar_seq_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`, `topic`] >> simp[] >>
  conj_tac >- suspend "inv" >>
  irule ghost_kept_readonly_transport >> goal_assum (drule_at Any) >>
  qexistsl_tac [`G`, `sm`] >> simp[]
QED
Resume compile_encode_log_topic_scalar_seq_ptr_ghost[inv]:
  irule ghost_inv_readonly_transport >> goal_assum (drule_at Any) >>
  simp[] >>
  qpat_x_assum `t with vs_vars := s.vs_vars = s`
    (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED
Finalise compile_encode_log_topic_scalar_seq_ptr_ghost
