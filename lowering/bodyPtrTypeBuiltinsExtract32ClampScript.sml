Theory bodyPtrTypeBuiltinsExtract32Clamp
Ancestors
  extract32Certificate
  augAssignPtrScalarClamp augAssignPtrScalarCertificate augAssignPtrScalarRun
  augAssignPtrScalarFrame
  bodyPtrTypeBuiltinsExtract32BoundsPtr exprSimExtract32Read
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  venomInst venomState venomExecSemantics ptrDiscipline fragGasSeqPtr
  list pred_set finite_map

(* Integer branches reuse the generic scalar clamp interface. The remaining
   basetypes either return unchanged or perform a scalar check of the word. *)
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
