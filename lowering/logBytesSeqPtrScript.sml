(* Concrete checked bytestring-copy sequences; input padding may be tainted. *)
Theory logBytesSeqPtr
Ancestors bodyPtrIfExpBytesCounted logBytesCodePtr logInstSeqPtr logTopicScalarPtr typedCopyPtr fragGasSeqPtr ghostPcTransportPtr
  context compileEnv loweringStateRelDefs exprSimBufferStore emitHelperProps emitHelper fragExec fragExecPtr exprLoweringProps
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
  drule_all bodyPtrIfExpBytesCountedTheory.compile_bytestring_copy_len_seq_ptr >>
  disch_then (qspecl_then [`D`,`fn`,`PG`]
    (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  qpat_x_assum `(sf with vs_vars := _) = s` (fn th =>
    `sf.vs_memory = s.vs_memory` by (SUBST1_TAC (SYM th) >> simp[])) >>
  `tnf.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa sb) _ _ _`
       (irule_at Any) >>
     drule bodyPtrIfExpBytesCountedTheory.compile_bytestring_copy_len_stages >>
     strip_tac >> gvs[] >>
     drule_all bodyPtrIfExpBytesCountedTheory.copy_len_round_structure >>
     strip_tac >> imp_res_tac emitted_insts_emit_op >> gvs[mk_inst_def]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem compile_store_bytestring_seq_ptr:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword(:256) /\ n < dimword(:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def,comp_bind_def] >>
  pairarg_tac >> simp[LET_THM,pairTheory.pair_case_def] >> strip_tac >>
  rename1 `compile_bytestring_copy_len (Var src) sa = (count_op,sc)` >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS,LESS_EQ_ADD]) >>
  drule_all compile_bytestring_copy_len_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand count_op s1 = SOME (n2w n)` by
    (fs[] >> qspec_then `len` mp_tac buffer_round_size >>
     `(~31w:bytes32) = i2w (-32)` by
       (simp[integer_wordTheory.i2w_def] >> blastLib.BBLAST_TAC) >>
     pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
     simp[vfmConstantsTheory.word_size_def]) >>
  qabbrev_tac `u = s1 with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sc)` >>
  `lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
   eval_operand count_op u = SOME (n2w n) /\
   ptr_covers G1 tn1 src u (w2n ((n2w n):256 word)) /\
   ptr_covers G1 tn1 dst u (w2n ((n2w n):256 word))` by
    suspend "coverage" >>
  drule_all emit_mcopy_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tf` (qx_choose_then `t` strip_assume_tac))) >>
  suspend "compose_store"
QED
Resume compile_store_bytestring_seq_ptr[coverage]:
  qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` strip_assume_tac) >>
  qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` strip_assume_tac) >>
  `eval_operand count_op u = eval_operand count_op s1` by
    (Cases_on `count_op` >> gvs[Abbr `u`,eval_operand_def,lookup_var_def]) >>
  gvs[Abbr `u`, ptr_covers_def,lookup_var_def,w2n_n2w] >> metis_tac[]
QED
Resume compile_store_bytestring_seq_ptr[compose_store]:
  drule compile_bytestring_copy_len_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sc) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb) /\
   EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sc sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> gvs[mk_inst_def,is_terminator_def] >>
     res_tac >> gvs[is_terminator_def]) >>
  `tf.t_imm = tn1.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sc sb) _ _ _` (irule_at Any) >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s1.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tf` by
    (qunabbrev_tac `u` >>
     drule_all successful_seq_ptr_append >> strip_tac >> gvs[]) >>
  qexistsl_tac [`G1`,`tf`,`t with vs_inst_idx := s1.vs_inst_idx`] >>
  simp[] >> suspend "store_post"
QED
Resume compile_store_bytestring_seq_ptr[store_post]:
  `u.vs_memory = s.vs_memory` by simp[Abbr `u`] >>
  `(mcopy (w2n b) (w2n a) n u).vs_memory =
    (mcopy (w2n b) (w2n a) n s).vs_memory` by
    simp[mcopy_def,write_memory_with_expansion_def] >>
  conj_tac >- metis_tac[ADD_COMM] >>
  conj_tac
  >- (rpt strip_tac >>
      `i+1 <= w2n b \/ w2n b+n <= i` by decide_tac >>
      metis_tac[buffer_mcopy_exterior,ADD_COMM]) >>
  conj_tac
  >- (rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >>
      CCONTR_TAC >> gvs[] >> decide_tac) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  simp[op_taint_def,Abbr `u`,lookup_var_def,mcopy_def,write_memory_with_expansion_def]
QED
Finalise compile_store_bytestring_seq_ptr
