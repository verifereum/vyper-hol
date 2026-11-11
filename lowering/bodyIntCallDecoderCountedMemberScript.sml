(* Counted address preparation for recursive ABI decoder members. *)
Theory bodyIntCallDecoderCountedMember
Ancestors
  bodyIntCallDecoderCountedPrimitive abiDecoderMemberCode abiDecoderMemberSetup
  abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderReentry
  fragGasPath fragExec exprLoweringProps emitHelperProps compileEnv
  venomState venomInst instIdxIndep entrySinkExtraction words list rich_list arithmetic

Theorem intcall_decoder_member_setup_path:
  abi_decode_member_setup dst src opc base_op hi dyn ao vo st = (ops,st') /\
  abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    abi_decode_load opc (n2w (B + (sb + ao)) : bytes32) s = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t n. gas_path ctx func s n (OK t) /\
    eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def]
QED
