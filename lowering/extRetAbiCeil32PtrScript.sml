Theory extRetAbiCeil32Ptr
Ancestors
  logAbiPrefixPtr abiEncoderBytesCode extRetAbiBytesArithPtr
  assignTuplePtrLocalCopyRun bodyPtrIfExpBytesFrame
  emitHelper emitHelperProps exprLoweringProps compileEnv context
  venomInst venomExecSemantics venomState ptrDiscipline
  fragGasSeqPtr fragGasPathPtr fragExec loweringStateRelDefs
  words list rich_list arithmetic

Overload ceil32[local] = ``contractABI$ceil32``

Theorem abi_encode_ceil32_shape:
  abi_encode_ceil32 len sa = (out,sb) ==>
  sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\ inst_extends sa sb /\
  out = Var (STRING #"%" (toString (sa.cs_next_var + 2))) /\
  EVERY (\i. MEM i.inst_opcode [NOT; ADD; AND]) (emitted_insts sa sb)
Proof
  simp[abi_encode_ceil32_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, mk_inst_def]
QED

Theorem ceil32_pure_sequence_frame[local]:
  EVERY (\i. MEM i.inst_opcode [NOT; ADD; AND]) code /\
  run_inst_seq code s = OK t ==> t = s with vs_vars := t.vs_vars
Proof
  strip_tac >>
  irule (cj 1 run_inst_seq_protected_frame) >>
  qexistsl_tac [`\x. F`, `code`] >> simp[] >>
  rpt strip_tac >>
  `MEM i.inst_opcode [NOT; ADD; AND]` by
    (qpat_x_assum `EVERY _ code` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  gvs[step_inst_base_def, exec_pure1_def, exec_pure2_def, AllCaseEqs(), update_var_def]
QED

Theorem abi_encode_ceil32_ambient_counted_ptr:
  abi_encode_ceil32 len sa = (Var out,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand len s = SOME (n2w n) /\
  op_taint tn len = {} /\ n <= dimword(:256) - 32 /\
  (!v. len = Var v ==> not_fresh_at sa v) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (ceil32 n)) /\
    op_taint tnf (Var out) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule abi_encode_ceil32_shape >> strip_tac >>
  drule_all abi_encode_ceil32_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `sf = s with vs_vars := sf.vs_vars` by
    (irule ceil32_pure_sequence_frame >> qexists_tac `emitted_insts sa sb` >> simp[]) >>
  `tnf.t_imm = tn.t_imm` by
    (drule_at Any inst_seq_ptr_immutable_frame >>
     impl_tac >-
       (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  conj_tac >-
    (irule emitted_sequence_path_ptr >> simp[] >> qexists_tac `sa` >>
     simp[same_blocks_def]) >>
  gvs[eval_operand_def, abi_bytes_round_mask_first, abi_bytes_ceil32_eq,
      lookup_var_def] >>
  qpat_x_assum `sf = s with vs_vars := _` SUBST_ALL_TAC >> simp[]
QED
