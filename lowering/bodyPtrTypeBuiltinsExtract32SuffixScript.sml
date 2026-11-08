Theory bodyPtrTypeBuiltinsExtract32Suffix
Ancestors
  bodyPtrTypeBuiltinsExtract32Read bodyPtrTypeBuiltinsExtract32Clamp
  exprSimExtract32Read exprSimExtract32Post exprLoweringProps emitHelperProps
  builtinBytes compileEnv freshWrites instSeqComposePtr fragGasSeqPtr ptrDiscipline
  venomInst venomState venomExecSemantics list pred_set finite_map words
  augAssignPtrScalarCertificate

Theorem extract32_load_result_available:
  compile_extract32_load len data offset sa = (raw,sb) ==>
  ?out. raw = Var out /\ not_fresh_at sb out
Proof
  strip_tac >> drule extract32_load_compiler_cuts >> strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_SUC_REFL]
QED

Theorem extract32_tail_code_cuts:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) ==>
  emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
  sa.cs_next_var <= sm.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sa.cs_next_var <= sm.cs_next_var` by
    (mp_tac (Q.SPECL [`len`,`data`,`offset`] extract32_read_load) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >> simp[]) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (mp_tac (Q.SPECL [`raw`,`typ`] extract32_read_clamp_basetype) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >> simp[]) >>
  conj_tac >- (irule emitted_insts_append >> simp[]) >> simp[] >>
  drule_all extract32_tail_straight_noext >> simp[EVERY_MEM]
QED

Theorem extract32_tail_bounds_normal_certificate:
  compile_extract32_load len (Var data) offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  not_fresh_at sa data /\
  (!z. offset = Var z \/ len = Var z ==> not_fresh_at sa z) /\
  scalar_available A offset /\ scalar_available A len /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  lookup_var data s = SOME a /\ eval_operand offset s = SOME b /\
  eval_operand len s = SOME l /\ w2n b + 32 <= w2n l /\
  ptr_covers G tn data s span /\ w2n b + 32 <= span /\
  w2n a + w2n b < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a + w2n b <= i /\ i < w2n a + w2n b + 32 ==> i NOTIN tn.t_mem) ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    op_prov H result = NONE /\ op_taint th result = {} /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  drule_all extract32_load_normal_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule extract32_load_result_available >> strip_tac >>
  `?J un.
    (!k. inst_seq_ptr D 0 ctx fn PG H th (emitted_insts sm sb)
      (t with vs_inst_idx := k) J un) /\
    result = Var out /\ op_prov J result = NONE /\ op_taint un result = {} /\
    (!p. not_fresh_at sm p ==> FLOOKUP J p = FLOOKUP H p /\
      op_taint un (Var p) = op_taint th (Var p)) /\
    un.t_mem = th.t_mem /\ un.t_stor = th.t_stor /\
    un.t_trans = th.t_trans /\ un.t_imm = th.t_imm` by
    (irule clamp_basetype_fixed_certificate >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`J`,`un`] >> simp[] >>
  conj_tac >- (irule inst_seq_ptr_uniform_append >> simp[] >>
    conj_tac >- (qexistsl_tac [`H`,`th`] >> simp[]) >>
    gvs[EVERY_CONJ, EVERY_APPEND]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem extract32_tail_bounds_abort_certificate:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  (!z. offset = Var z \/ len = Var z ==> not_fresh_at sa z) /\
  scalar_available A offset /\ scalar_available A len /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  eval_operand offset s = SOME b /\ eval_operand len s = SOME l /\
  ~(w2n b + 32 <= w2n l) /\ ~ctx_has_dalloca ctx ==>
  ?H th t.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  drule_all extract32_load_abort_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`,`t`] >> simp[run_inst_seq_append_err] >>
  irule inst_seq_ptr_uniform_abort_append >> simp[] >> gvs[EVERY_APPEND, EVERY_CONJ]
QED

Theorem extract32_tail_normal_ptr_path:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  gvs[EVERY_CONJ] >>
  drule_all (SRULE [EVERY_CONJ, EVERY_APPEND] (Q.SPEC `xs ++ ys` run_inst_seq_gas_path_ptr)) >> simp[]
QED

Theorem extract32_tail_abort_ptr_path:
  compile_extract32_load len data offset sa = (raw,sm) /\
  compile_clamp_basetype raw typ sm = (result,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?n j. gas_path_ptr D 0 ctx fn PG G tn s n H th
    (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all extract32_tail_code_cuts >> strip_tac >>
  gvs[EVERY_CONJ] >>
  drule_all (SRULE [EVERY_CONJ, EVERY_APPEND]
    (Q.SPEC `xs ++ ys` run_inst_seq_abort_gas_path_ptr)) >> simp[]
QED
