(* Concrete checked bytestring-copy sequences; input padding may be tainted. *)
Theory logBytesSeqPtr
Ancestors logInstSeqPtr logTopicScalarPtr typedCopyPtr fragGasSeqPtr ghostPcTransportPtr
  context compileEnv emitHelperProps emitHelper fragExec fragExecPtr exprLoweringProps
  bodyPtrDefs ptrSafeRun ptrDiscipline
  venomInst venomState venomExecSemantics codegenRel finite_map words list arithmetic

Theorem compile_bytestring_copy_len_seq_ptr:
  compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand count_op sf =
      SOME ((mload (w2n a) s + 31w && i2w (-32)) + 32w) /\
    op_taint tnf count_op = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  ntac 3 (pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def]) >> strip_tac >>
  `?v1. src_len = Var v1` by
    (qpat_assum `emit_op MLOAD _ _ = _`
      (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?v2. padded_len = Var v2` by
    (qpat_assum `emit_op ADD _ _ = (padded_len,_)`
      (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?v3. rounded = Var v3` by
    (qpat_assum `emit_op AND _ _ = _`
      (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  `?v4. count_op = Var v4` by
    (qpat_assum `emit_op ADD _ _ = (count_op,_)`
      (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (Var v1,sc1)` >>
  rename1 `emit_op ADD [Var v1;Lit 31w] sc1 = (Var v2,sc2)` >>
  rename1 `emit_op AND [Var v2;Lit (i2w (-32))] sc2 = (Var v3,sc3)` >>
  drule_all emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  suspend "round"
QED
Resume compile_bytestring_copy_len_seq_ptr[round]:
  qabbrev_tac `u1 = s1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sc1)` >>
  `eval_operand (Var v1) u1 = SOME (mload (w2n a) s) /\
   eval_operand (Lit 31w) u1 = SOME 31w /\ op_taint tn1 (Lit 31w) = {}` by
    gvs[Abbr `u1`, eval_operand_def, lookup_var_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G1`,`D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qabbrev_tac `u2 = s2 with vs_inst_idx := u1.vs_inst_idx + LENGTH (emitted_insts sc1 sc2)` >>
  `eval_operand (Var v2) u2 = SOME (mload (w2n a) s + 31w) /\
   eval_operand (Lit (i2w (-32))) u2 = SOME (i2w (-32)) /\
   op_taint tn2 (Lit (i2w (-32))) = {}` by
    gvs[Abbr `u2`, eval_operand_def, lookup_var_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G2`,`D`]
    (qx_choose_then `G3` (qx_choose_then `tn3` (qx_choose_then `s3` strip_assume_tac)))) >>
  qabbrev_tac `u3 = s3 with vs_inst_idx := u2.vs_inst_idx + LENGTH (emitted_insts sc2 sc3)` >>
  `eval_operand (Var v3) u3 = SOME (mload (w2n a) s + 31w && i2w (-32)) /\
   eval_operand (Lit 32w) u3 = SOME 32w /\ op_taint tn3 (Lit 32w) = {}` by
    gvs[Abbr `u3`, eval_operand_def, lookup_var_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G3`,`D`]
    (qx_choose_then `G4` (qx_choose_then `tn4` (qx_choose_then `s4` strip_assume_tac)))) >>
  suspend "compose"
QED
Resume compile_bytestring_copy_len_seq_ptr[compose]:
  `emitted_insts sc2 sb = emitted_insts sc2 sc3 ++ emitted_insts sc3 sb /\
   emitted_insts sc1 sb = emitted_insts sc1 sc2 ++ emitted_insts sc2 sb /\
   emitted_insts sa sb = emitted_insts sa sc1 ++ emitted_insts sc1 sb` by
    (imp_res_tac emitted_insts_emit_op >>
     conj_asm1_tac >- (irule emitted_insts_append >> simp[]) >>
     conj_asm1_tac >- (irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
     irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (s4 with vs_inst_idx := s1.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G4 tn4` by
    suspend "runs" >>
  qexistsl_tac [`G4`,`tn4`,`s4 with vs_inst_idx := s1.vs_inst_idx`] >>
  `tn4.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa sb) _ _ _` (irule_at Any) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  simp[eval_operand_def, lookup_var_def] >>
  suspend "frame"
QED
Resume compile_bytestring_copy_len_seq_ptr[runs]:
  rpt (qpat_x_assum `!p. not_fresh_at _ p ==> _` kall_tac) >>
  rpt (qpat_x_assum `eval_operand _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `lookup_var _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `op_taint _ _ = _` kall_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc3 sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc2 sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc1 sb)` by
    (imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def]) >>
  `run_inst_seq (emitted_insts sc2 sb) u2 = OK (s4 with vs_inst_idx := s3.vs_inst_idx)` by
    (qpat_assum `emitted_insts sc2 sb = _` SUBST1_TAC >>
     irule run_inst_seq_append_advanced >> simp[GSYM markerTheory.Abbrev_def] >>
     qexistsl_tac [`s3`,`s4`] >> simp[GSYM markerTheory.Abbrev_def] >>
     fs[Abbr `u3`]) >>
  suspend "runs_rest"
QED
Resume compile_bytestring_copy_len_seq_ptr[runs_rest]:
  `run_inst_seq (emitted_insts sc1 sb) u1 = OK (s4 with vs_inst_idx := s2.vs_inst_idx)` by
    (qpat_assum `emitted_insts sc1 sb = _` SUBST1_TAC >>
     `s4 with vs_inst_idx := s2.vs_inst_idx =
        (s4 with vs_inst_idx := s3.vs_inst_idx) with vs_inst_idx := s2.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >> irule run_inst_seq_append_advanced >>
     gvs[Abbr `u2`]) >>
  conj_tac
  >- (qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      `s4 with vs_inst_idx := s1.vs_inst_idx =
        (s4 with vs_inst_idx := s2.vs_inst_idx) with vs_inst_idx := s1.vs_inst_idx` by simp[] >>
      pop_assum SUBST1_TAC >> irule run_inst_seq_append_advanced >>
      gvs[Abbr `u1`]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sc1) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sc1 sc2) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sc2 sc3)` by
    (imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def]) >>
  qunabbrev_tac `u3` >> qunabbrev_tac `u2` >> qunabbrev_tac `u1` >>
  qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
  irule inst_seq_ptr_append >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`s1`,`tn1`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `emitted_insts sc1 sb = _` SUBST1_TAC >>
  irule inst_seq_ptr_append >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G2`,`s2`,`tn2`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `emitted_insts sc2 sb = _` SUBST1_TAC >>
  irule inst_seq_ptr_append >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G3`,`s3`,`tn3`] >> simp[]
QED
Resume compile_bytestring_copy_len_seq_ptr[frame]:
  `!p. not_fresh_at sa p ==> not_fresh_at sc1 p /\
       not_fresh_at sc2 p /\ not_fresh_at sc3 p` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ sc1 = _` mp_tac >>
     qpat_x_assum `emit_op AND _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def,comp_bind_def,comp_ignore_bind_def,fresh_var_def,
       fresh_id_def,emit_def,comp_return_def,not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` kall_tac) >>
  gvs[Abbr `u1`,Abbr `u2`,Abbr `u3`,lookup_var_def] >>
  rpt strip_tac >>
  `not_fresh_at sc1 p /\ not_fresh_at sc2 p /\ not_fresh_at sc3 p` by metis_tac[] >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc1 p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc2 p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc3 p ==> _` (qspec_then `p` mp_tac) >> simp[]
QED
Finalise compile_bytestring_copy_len_seq_ptr
