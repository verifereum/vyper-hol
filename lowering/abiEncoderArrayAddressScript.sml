(* Execute the shared seven-instruction encoder body address prefix. *)
Theory abiEncoderArrayAddress
Ancestors
  abiEncoderArrayCode abiDecoderDynamicLoopSetup abiDecoderReentryAddress abiDecoderReentry
  abiDecoderGuards abiDecoderContract abiDecoderArrayHeader emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_encode_array_addresses_shape:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') ==>
  st'.cs_next_var = st.cs_next_var+7 /\ st'.cs_next_id = st.cs_next_id+7 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  abi_decoder_operand_live st'.cs_next_var (FST (FST coords)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (FST coords)) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND coords)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND coords)) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_encode_array_addresses_sequence:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (FST coords)) actual = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) actual = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_addresses_trace >> strip_tac >>
  drule abi_decode_array_head_setup_counters >> strip_tac >>
  drule abi_decode_indexed_coordinates_counters >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `st'` |-> `middle`, `ops` |-> `src_ops`,
    `abi_sz` |-> `msz:num`, `i` |-> `j:num`] abi_decode_array_head_setup_reentry) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) initial = OK ready` >>
  `eval_operand dst ready = SOME (n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`st` |-> `middle`, `base_op` |-> `dst`, `idx` |-> `FST (src_ops:operand # operand # operand)`,
    `stride` |-> `asz:num`, `s` |-> `ready:venom_state`, `i` |-> `j:num`,
    `sb` |-> `d:num`, `ops` |-> `dst_ops`] abi_decode_indexed_coordinates_reentry) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts middle st') ready = OK actual` >>
  `eval_operand (FST src_ops) actual = SOME (n2w j) /\
    eval_operand (SND (SND src_ops)) actual = SOME (n2w (sb+32+j*msz))` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st st') initial = OK actual /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`ready`, `middle`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`middle.cs_next_var`, `ready`] >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_ADDRESS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array address setup not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayAddress");
