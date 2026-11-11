(* S3 frame for an actual straight-line encoder sequence. *)
Theory abiEncoderWindowSequenceFrameMem
Ancestors
  abiEncoderWindowMemFrame abiEncoderWindowSequence emitHelperProps
  stmtReasonLitFragMemory abiDecoderVarSequence
  exprLoweringProps fragExec venomState venomExecSemantics venomInst list rich_list

Theorem window_seq_mem_frame:
  window_seq st en s raw /\ fn_has_code st en func /\
  fn_inst_ids_distinct func /\ alloca_inv s /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode \/
    MEM i.inst_opcode [SUB;Div;Mod;AND;OR;XOR;NOT;SAR;ASSIGN;NOP])
    (emitted_insts st en) ==>
  window_mem_frame ctx func s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >>
  `en.cs_current_insts = st.cs_current_insts ++ emitted_insts st en` by
    fs[window_seq_def, inst_extends_def, exprLoweringPropsTheory.emitted_insts_def] >>
  `en.cs_current_bb = st.cs_current_bb` by fs[window_seq_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st en ++ rest` by
    gvs[IS_PREFIX_APPEND] >>
  `LENGTH en.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts st en)` by simp[] >>
  `window_mem_frame ctx func s
    (raw with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st en))`
    suffices_by metis_tac[] >>
  irule window_mem_frame_sequence >>
  goal_assum (drule_at Any) >>
  fs[window_seq_def, EVERY_MEM] >> metis_tac[]
QED
