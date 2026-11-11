(* Physical checks for the emitted dynamic-array header, stopping before JNZ. *)
Theory extcallDecoderHeaderMemory
Ancestors
  abiDecoderExecution fragExecMem instMemFrontier venomExecSemantics
  venomInstProofs venomState venomInst memSafeRun ssaOperandFrame emitHelperProps
  words arithmetic list rich_list

Theorem extcall_decoder_header_prefix_mem_ok:
  abi_decode_position_loop_ready hdr ip src MLOAD base_op B sb p c j s /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  B+sb < dimword(:256) /\
  w2n p+32 <= s.vs_alloca_next /\
  B+sb+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    (FRONT (abi_decode_position_header_insts id ip src MLOAD base_op first
      body_lbl exit_lbl)) s
Proof
  strip_tac >>
  fs[abi_decode_position_loop_ready_def] >>
  `eval_operand src (update_var (STRING #"%" (toString first)) (n2w j) s) =
     SOME (n2w sb)` by simp[eval_operand_update_var_avoids] >>
  `eval_operand base_op (update_var (STRING #"%" (toString first)) (n2w j) s) =
     SOME (n2w B)` by simp[eval_operand_update_var_avoids] >>
  `!name w t. (update_var name w t).vs_alloca_next = t.vs_alloca_next` by
    simp[update_var_def] >>
  Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_position_header_insts_def,
       abi_decode_position_header_delta_def, FRONT_DEF] >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_MLOAD,
       inst_dload_in_section_def, mk_inst_def] >>
  simp[Once step_inst_base_def, exec_read1_def]
  >- (simp[Once run_inst_seq_mem_ok_def, GSYM mk_inst_def,
           below_frontier_MLOAD, w2n_n2w] >>
      simp[Once step_inst_base_def, mk_inst_def, exec_read1_def] >>
      irule run_inst_seq_mem_ok_every >>
      simp[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       inst_dload_in_section_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, word_add_n2w] >>
  simp[Once run_inst_seq_mem_ok_def, GSYM mk_inst_def,
       below_frontier_MLOAD, eval_operand_def, lookup_var_update_var,
       w2n_n2w] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def,
       eval_operand_def, lookup_var_update_var] >>
  irule run_inst_seq_mem_ok_every >>
  simp[below_frontier_no_ranges, inst_dload_in_section_def]
QED
