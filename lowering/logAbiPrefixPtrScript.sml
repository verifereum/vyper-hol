(* Pointer checks and ghost frames for the bytes encoder's arithmetic phases. *)
Theory logAbiPrefixPtr
Ancestors
  logInstSeqPtr abiEncoderBytesCode abiEncoderRounding
  typedCopyPtr fragExecPtr fragExec ptrDiscipline ptrSafeRun
  emitHelperProps emitHelper compileEnv context exprLoweringProps
  venomExecSemantics venomState venomInst finite_map words list arithmetic

Theorem abi_encode_round_seq_ptr:
  abi_encode_round len sa = (out,sb) /\
  eval_operand len s = SOME w /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand out sf = SOME
      (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w && (31w+w)) /\
    op_taint tnf out = {} /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Lit 31w;len] sa = (arg,sm)` >>
  `?tmp. arg = Var tmp` by (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?res. out = Var res` by
    (qpat_assum `emit_op AND _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  gvs[] >>
  `eval_operand (Lit 31w) s = SOME 31w /\ op_taint tn (Lit 31w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `t` strip_assume_tac)))) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand (Var tmp) u = SOME (31w+w) /\
   eval_operand (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) u =
     SOME 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w /\
   op_taint tn1 (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) = {}` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `G1`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `v` strip_assume_tac)))) >>
  qexistsl_tac [`Gf`, `tnf`, `v with vs_inst_idx := t.vs_inst_idx`] >>
  conj_tac >- suspend "run" >>
  conj_tac >- suspend "checks" >>
  suspend "frame"
QED

Resume abi_encode_round_seq_ptr[run]:
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (imp_res_tac emitted_insts_emit_op >> irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (qpat_assum `emit_op AND _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> simp[]
QED
Resume abi_encode_round_seq_ptr[checks]:
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (imp_res_tac emitted_insts_emit_op >> irule emitted_insts_append >> simp[]) >>
  once_asm_rewrite_tac[] >> irule inst_seq_ptr_append >>
  conj_tac >-
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`G1`, `t`, `tn1`] >> gvs[Abbr `u`]
QED
Resume abi_encode_round_seq_ptr[frame]:
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  gvs[Abbr `u`, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED
Finalise abi_encode_round_seq_ptr
