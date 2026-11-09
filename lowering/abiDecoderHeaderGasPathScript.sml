Theory abiDecoderHeaderGasPath
Ancestors
  abiDecoderExecution fragGasSeq fragGasPath abiDecoderContract
  venomExecSemantics venomInst venomInstProofs venomState words list arithmetic

Theorem abi_decode_ready_header_gas_path:
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl id ip src opc iv cv cmp done /\
  abi_decode_loop_ready hdr ip src opc p srcaddr ncount j s /\
  abi_decode_source_opcode opc /\ src <> Var iv /\ iv <> cv /\
  ncount < dimword(:256) ==>
  gas_path ctx fn s 0
    (OK (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done j ncount s)))
Proof
  strip_tac >>
  gvs[abi_decode_loop_cfg_def, abi_decode_loop_ready_def] >>
  `run_inst_seq (TAKE 4 (abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl)) s =
     OK (abi_decode_header_state iv cv cmp done j ncount s)` by
    (irule abi_decode_header_prefix >> simp[] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `fn`,
    `<|bb_label := s.vs_current_bb; bb_instructions :=
      abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl|>`] mp_tac) >>
  impl_tac >- fs[abi_decode_header_insts_def, abi_decode_source_opcode_def,
    mk_inst_def, is_terminator_def] >>
  simp[abi_decode_header_insts_def, mk_inst_def, abi_decode_source_opcode_def] >>
  strip_tac >>
  `opc <> GAS` by fs[abi_decode_source_opcode_def] >> gvs[] >>
  qabbrev_tac `h = abi_decode_header_state iv cv cmp done j ncount s with vs_inst_idx := 4` >>
  `gas_path_edge ctx fn h 0
    (OK (jump_to (if j < ncount then body_lbl else exit_lbl) h))` by
    (simp[gas_path_edge_def, Abbr `h`, abi_decode_header_state_def, update_var_def] >>
     qexistsl [`0`, `mk_inst (id+4) JNZ [Var done;Label exit_lbl;Label body_lbl] []`] >>
     simp[get_instruction_def, abi_decode_header_insts_def, step_inst_def,
       step_inst_base_opcode_eqs, mk_inst_def, gasCountTheory.gas_count_step_def,
       is_terminator_def, eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `j < ncount` >> simp[bool_to_word_def] >> metis_tac[]) >>
  `~h.vs_halted` by simp[Abbr `h`, abi_decode_header_state_def, update_var_def] >>
  `gas_path ctx fn h 0 (OK (jump_to (if j < ncount then body_lbl else exit_lbl) h))` by
    (`~(jump_to (if j < ncount then body_lbl else exit_lbl) h).vs_halted` by
       simp[jump_to_def] >> metis_tac[gas_path_rules, ADD_0]) >>
  drule_all gas_path_then >>
  simp[Abbr `h`, jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem abi_decode_backedge_gas_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) ==>
  gas_path ctx fn s 0
    (OK (jump_to hdr (mstore (w2n p) (n2w (SUC i))
      (update_var nv (n2w (SUC i)) s))))
Proof
  strip_tac >> drule_all abi_decode_increment_prefix >>
  disch_then (qspecl_then [`id`, `hdr`] assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `fn`, `bb`] mp_tac) >>
  impl_tac >- simp[abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def,
    rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[abi_decode_backedge_insts_def, mk_inst_def] >> strip_tac >>
  qabbrev_tac `h = mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)
    with vs_inst_idx := LENGTH prefix + 2` >>
  `gas_path ctx fn h 0 (OK (jump_to hdr h))` by
    (irule gas_path_jump >>
     conj_tac >- simp[Abbr `h`, mstore_def, update_var_def, write_memory_with_expansion_def] >>
     qexistsl [`bb`, `id+2`, `prefix ++ TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)`] >>
     simp[Abbr `h`, abi_decode_backedge_insts_def, mstore_def, update_var_def,
       write_memory_with_expansion_def]) >>
  drule_all gas_path_then >>
  simp[Abbr `h`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED
