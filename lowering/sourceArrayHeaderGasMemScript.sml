Theory sourceArrayHeaderGasMem
Ancestors
  abiDecoderExecution abiDecoderContract fragGasSeqMem fragGasPathMem fragExecMem
  instMemFrontier memSafeRun gasCount venomExecSemantics venomExecProofs
  venomState venomInst emitHelperProps exprLoweringProps words arithmetic list rich_list

Theorem source_array_header_gas_path_mem:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w i /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s)))
Proof
  strip_tac >>
  `run_inst_seq (TAKE 4 (abi_decode_header_insts id ip src CALLDATALOAD
      iv cv cmp done body_lbl exit_lbl)) s =
    OK (abi_decode_header_state iv cv cmp done i ncount s)` by
    (irule abi_decode_header_prefix >> simp[abi_decode_source_opcode_def]) >>
  `run_inst_seq_mem_ok (TAKE 4 (abi_decode_header_insts id ip src CALLDATALOAD
      iv cv cmp done body_lbl exit_lbl)) s` by
    (simp[abi_decode_header_insts_def, Once run_inst_seq_mem_ok_def,
      below_frontier_MLOAD, inst_dload_in_section_other] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
     irule run_inst_seq_mem_ok_every >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `fn`,
    `<|bb_label := hdr; bb_instructions := abi_decode_header_insts id ip src
        CALLDATALOAD iv cv cmp done body_lbl exit_lbl|>`] mp_tac) >>
  simp[abi_decode_header_insts_def, mk_inst_def, is_terminator_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s 0 (OK h)` >>
  `gas_path_mem_edge ctx fn h 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s)))` by
    (simp[gas_path_mem_edge_def, Abbr `h`, abi_decode_header_state_def,
       update_var_def] >> qexists_tac `0` >>
     simp[abi_decode_header_state_def, update_var_def,
       get_instruction_def, abi_decode_header_insts_def,
       step_inst_def, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       gas_count_step_def, mem_safe_step_non_invoke,
       below_frontier_no_ranges, inst_dload_in_section_other,
       is_terminator_def] >>
     Cases_on `i < ncount` >> simp[bool_to_word_def, jump_to_def] >>
     metis_tac[]) >>
  `~(jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s)).vs_halted` by
    simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  `gas_path_mem ctx fn h (0+0)
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s)))` by
    (irule (cj 2 gas_path_mem_rules) >>
     goal_assum (drule_at Any) >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED
