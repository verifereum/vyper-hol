Theory bodyPtrTypeBuiltinsExtract32Clamp
Ancestors
  augAssignPtrScalarClamp augAssignPtrScalarCertificate augAssignPtrScalarRun
  augAssignPtrScalarFrame
  bodyPtrTypeBuiltinsExtract32BoundsPtr exprSimExtract32Read
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  venomInst venomState venomExecSemantics ptrDiscipline fragGasSeqPtr
  list pred_set finite_map

(* Integer branches reuse the generic scalar clamp interface. The remaining
   basetypes either return unchanged or perform a scalar check of the word. *)
Theorem scalar_clamp_basetype_code:
  compile_clamp_basetype raw typ sa = (result,sb) /\ scalar_available A raw ==>
  scalar_code A (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `typ` >>
  gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
  Cases_on `b`
  >~ [`compile_clamp_basetype raw (BaseT (UintT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
     drule_all scalar_clamp_and_return_code >> simp[])
  >~ [`compile_clamp_basetype raw (BaseT (IntT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
     drule_all scalar_clamp_and_return_code >> simp[])
  >~ [`compile_clamp_basetype raw (BaseT (BytesT bt)) sa = _`] >-
    (Cases_on `bt` >>
     gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def,
         AllCaseEqs()] >> suspend "bytes") >>
  gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
  suspend "address"
QED

Resume scalar_clamp_basetype_code[bytes]:
  Cases_on `n < 32` >> gvs[comp_return_def, emitted_insts_refl, scalar_code_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def] >> rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND,
       scalar_code_def, scalar_shape_def, scalar_binary_def, scalar_unary_def,
       mk_inst_def, scalar_available_def] >>
  gvs[scalar_available_def]
QED

Resume scalar_clamp_basetype_code[address]:
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def] >> rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND,
       scalar_code_def, scalar_shape_def, scalar_binary_def, scalar_unary_def,
       mk_inst_def, scalar_available_def] >>
  gvs[scalar_available_def]
QED
Finalise scalar_clamp_basetype_code

Theorem clamp_basetype_returns_input:
  compile_clamp_basetype raw typ sa = (result,sb) ==> result = raw
Proof
  strip_tac >> Cases_on `typ` >> gvs[compile_clamp_basetype_def, comp_return_def] >>
  Cases_on `b`
  >~ [`compile_clamp_basetype raw (BaseT (UintT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, clamp_and_return_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[])
  >~ [`compile_clamp_basetype raw (BaseT (IntT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, clamp_and_return_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[])
  >~ [`compile_clamp_basetype raw (BaseT (BytesT bt)) sa = _`] >-
    (Cases_on `bt` >> gvs[compile_clamp_basetype_def, comp_return_def] >>
     Cases_on `n < 32` >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem clamp_basetype_fixed_certificate:
  compile_clamp_basetype (Var x) typ sa = (result,sb) /\
  not_fresh_at sa x /\ op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?H th.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H th) /\
    result = Var x /\ op_prov H result = NONE /\ op_taint th result = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `result = Var x` by metis_tac[clamp_basetype_returns_input] >>
  `scalar_code {x} (emitted_insts sa sb)` by
    (irule scalar_clamp_basetype_code >> simp[scalar_available_def] >> metis_tac[]) >>
  `!v. v IN {x} ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by simp[] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`,`s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  `!p. not_fresh_at sa p ==>
    ~MEM p (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (mp_tac (Q.SPECL [`Var x`,`typ`] extract32_read_clamp_basetype) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >>
     simp[EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  qexistsl_tac [`H`,`tm`] >> simp[] >>
  conj_tac >- (irule scalar_code_certificate_cursor >> simp[] >>
    qexists_tac `{x}` >> simp[]) >>
  gvs[op_prov_def] >> metis_tac[]
QED

Theorem clamp_basetype_normal_ptr_path:
  compile_clamp_basetype (Var x) typ sa = (result,sb) /\
  not_fresh_at sa x /\ op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    result = Var x /\ op_prov H result = NONE /\ op_taint th result = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all clamp_basetype_fixed_certificate >>
  disch_then (qspecl_then [`s`,`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  `scalar_code {x} (emitted_insts sa sb)` by
    (irule scalar_clamp_basetype_code >> simp[scalar_available_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule scalar_code_shapes >> simp[EVERY_MEM] >> metis_tac[scalar_shape_control]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  gvs[EVERY_CONJ] >> drule_all (SRULE [EVERY_CONJ] run_inst_seq_gas_path_ptr) >> simp[]
QED

Theorem clamp_basetype_abort_ptr_path:
  compile_clamp_basetype (Var x) typ sa = (result,sb) /\
  not_fresh_at sa x /\ op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th
      (Abort err (t with vs_inst_idx := j)) /\
    result = Var x /\ op_prov H result = NONE /\ op_taint th result = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all clamp_basetype_fixed_certificate >>
  disch_then (qspecl_then [`s`,`fn`,`PG`,`D`] strip_assume_tac) >>
  `scalar_code {x} (emitted_insts sa sb)` by
    (irule scalar_clamp_basetype_code >> simp[scalar_available_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (drule scalar_code_shapes >> simp[EVERY_MEM] >> metis_tac[scalar_shape_control]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED
