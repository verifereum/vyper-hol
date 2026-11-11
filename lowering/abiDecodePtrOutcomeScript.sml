(* Actual-start paths obtained from normalized whole-interval certificates. *)
Theory abiDecodePtrOutcome
Ancestors
  abiDecodePtrRejectSequence abiDecodePtrReentry abiDecoderVarExtend
  abiDecodePtrRejectChecks abiDecoderVarSequence
  fragGasSeqPtr stmtReasonLitFragMemory exprLoweringProps fragExec emitHelperProps compileEnv venomExecSemantics
  venomState venomInst list rich_list

Theorem abi_decode_actual_reject_path:
  fn_has_code sa sb func /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  abi_decoder_vars_extend extras r s /\
  abi_decode_reject_witness (emitted_insts sa sb) r u /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) r H tf ==>
  ?v n j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort v /\
    vsr_term_frame u = vsr_term_frame v /\
    gas_path_ptr D lo ctx func PG G tn s n H tf
      (Abort Revert_abort (v with vs_inst_idx := j))
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all abi_decode_ptr_reject_sequence_extend >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[] >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem abi_decode_actual_success_path:
  fn_has_code sa sb func /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  abi_decoder_vars_extend extras r s /\
  run_inst_seq (emitted_insts sa sb) r = OK u /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) r H tf ==>
  ?v. run_inst_seq (emitted_insts sa sb) s = OK v /\
    abi_decoder_vars_extend extras u v /\
    gas_path_ptr D lo ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H tf
      (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule_all abi_decode_ptr_sequence_extend >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> abi_decoder_reentry_opcode _ /\ _`
       drule >> simp[abi_decoder_reentry_opcode_def] >>
     metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    metis_tac[LENGTH_APPEND] >>
  strip_tac >> goal_assum (drule_at Any) >> gvs[]
QED
