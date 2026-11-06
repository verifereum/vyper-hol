Theory bodyPtrTypeBuiltinsScalarChecks
Ancestors
  bodyPtrTypeBuiltinsClamp exprLowering exprLoweringProps fragGasSeqPtr
  compileEnv ptrDiscipline finite_map venomState venomInst list

Theorem convert_address_clamp:
  compile_type_convert x ConvToAddress = compile_int_clamp F 160 x
Proof
  simp[compile_type_convert_def, compile_int_clamp_def]
QED

Theorem convert_address_fixed_certificate:
  compile_type_convert x ConvToAddress sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rewrite_tac[convert_address_clamp] >>
  MATCH_ACCEPT_TAC int_clamp_unsigned_fixed_certificate
QED

Theorem convert_flag_fixed_certificate:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `n < 256`
  >- (simp[compile_type_convert_def] >>
      MATCH_ACCEPT_TAC int_clamp_unsigned_fixed_certificate) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`G`,`tn`] >>
  simp[emitted_insts_def, inst_seq_ptr_def]
QED

Theorem convert_address_runtime_frame:
  compile_type_convert x ConvToAddress sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  rewrite_tac[convert_address_clamp] >> MATCH_ACCEPT_TAC int_clamp_runtime_frame
QED

Theorem convert_flag_runtime_frame:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  Cases_on `n < 256`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_runtime_frame) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem convert_address_instruction_filter:
  compile_type_convert x ConvToAddress sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  rewrite_tac[convert_address_clamp] >> MATCH_ACCEPT_TAC int_clamp_instruction_filter
QED

Theorem convert_flag_instruction_filter:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `n < 256`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_instruction_filter) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def]
QED
