(* Counted, real-state control paths for the memory decoder loop. *)
Theory abiDecodeMemLoopControl
Ancestors
  abiDecoderExecution abiDecodeMemScratch abiEncoderWindowControlMem
  fragGasSeqMem fragGasPathMem fragGasMode instMemFrontier memSafeRun
  venomExecSemantics venomExecProofs venomInstProofs venomState venomInst
  words arithmetic list rich_list ASCIInumbers fragExecMem exprLoweringProps emitHelperProps
  stmtForRangeMemoryParts abiDecoderContract allocaHistory localPtrsProps

Theorem abi_decode_position_header_mem_ok[local]:
  eval_operand ip s = SOME p /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  w2n p + 32 <= s.vs_alloca_next /\
  w2n (n2w (B+sb):bytes32) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    (TAKE (4 + abi_decode_position_header_delta base_op)
      (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl)) s
Proof
  strip_tac >>
  `!w. eval_operand src (update_var (STRING #"%" (toString first)) w s) = SOME (n2w sb)` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `!w. eval_operand base_op (update_var (STRING #"%" (toString first)) w s) = SOME (n2w B)` by
    (Cases_on `base_op` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  Cases_on `base_op = Lit 0w` >>
  gvs[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def,
      run_inst_seq_mem_ok_def, below_frontier_MLOAD, below_frontier_no_ranges,
      inst_dload_in_section_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, below_frontier_MLOAD, below_frontier_no_ranges,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure2_def,
       exec_pure1_def, eval_operand_update_var, lookup_var_update_var,
       word_add_n2w, AllCaseEqs(), toString_11] >>
  gvs[eval_operand_def, GSYM word_add_n2w] >>
  qpat_x_assum `_ + 32 <= _` mp_tac >>
  once_rewrite_tac[GSYM arithmeticTheory.MOD_PLUS] >>
  simp[lookup_var_update_var, toString_11]
QED

Theorem abi_decode_position_header_path_mem:
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl id ip src MLOAD base_op first /\
  abi_decode_position_loop_ready hdr ip src MLOAD base_op B sb p ncount i s /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  ncount < dimword(:256) /\ w2n p + 32 <= s.vs_alloca_next /\
  w2n (n2w (B+sb):bytes32) + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B sb i ncount s)))
Proof
  strip_tac >>
  fs[abi_decode_position_loop_cfg_def, abi_decode_position_loop_ready_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_position_header_prefix >> strip_tac >>
  `run_inst_seq_mem_ok (TAKE (4+abi_decode_position_header_delta base_op)
    (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl)) s` by
    (irule abi_decode_position_header_mem_ok >> simp[] >> qexistsl_tac [`B`,`sb`] >> simp[]) >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
    (TAKE (4+abi_decode_position_header_delta base_op)
      (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))` by
    (Cases_on `base_op = Lit 0w` >>
     simp[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def,
          mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx fn s
    (LENGTH (FILTER (\inst. inst.inst_opcode = GAS)
      (TAKE (4+abi_decode_position_header_delta base_op)
        (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))))
    (OK (abi_decode_position_header_state base_op first B sb i ncount s with
      vs_inst_idx := s.vs_inst_idx + LENGTH
        (TAKE (4+abi_decode_position_header_delta base_op)
          (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))))` by
    (irule run_inst_seq_gas_path_mem >> simp[] >>
     Cases_on `base_op = Lit 0w` >>
     simp[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s _ (OK t)` >>
  `~t.vs_halted` by
    (Cases_on `base_op = Lit 0w` >>
     simp[Abbr `t`, abi_decode_position_header_state_def, update_var_def]) >>
  `gas_path_mem ctx fn t 0
    (OK (jump_to (if bool_to_word (~(i < ncount)) <> 0w then exit_lbl else body_lbl) t))` by
    (irule for_range_jnz_zero_path_mem >>
     simp[Abbr `t`, abi_decode_position_header_state_def, update_var_def] >>
     qexistsl_tac [`<|bb_label := hdr; bb_instructions :=
       abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl|>`,
       `id+4+abi_decode_position_header_delta base_op`,
       `Var (STRING #"%" (toString (first+3+abi_decode_position_header_delta base_op)))`] >>
     Cases_on `base_op = Lit 0w` >>
     simp[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def,
          get_instruction_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  drule_all gas_path_mem_then >>
  Cases_on `base_op = Lit 0w` >> Cases_on `i < ncount` >>
  gvs[Abbr `t`, abi_decode_position_header_insts_def, abi_decode_position_header_delta_def,
      mk_inst_def, bool_to_word_def, jump_to_def]
QED

Theorem abi_decode_backedge_prefix_mem_ok[local]:
  eval_operand ip s = SOME p /\ ip <> Var nv /\
  w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s
Proof
  strip_tac >>
  `!w. eval_operand ip (update_var nv w s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  simp[abi_decode_backedge_insts_def, run_inst_seq_mem_ok_def,
       below_frontier_no_ranges, mk_inst_def, inst_dload_in_section_def] >>
  Cases_on `eval_operand (Var iv) s` >>
  simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_lit, below_frontier_MSTORE, exec_write2_def,
       eval_operand_update_var] >>
  simp[update_var_def]
QED

Theorem abi_decode_backedge_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to hdr
      (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))))
Proof
  strip_tac >> drule_all abi_decode_increment_prefix >> strip_tac >>
  `gas_path_mem ctx fn s
    (LENGTH (FILTER (\inst. inst.inst_opcode = GAS)
      (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr))))
    (OK (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s) with
      vs_inst_idx := s.vs_inst_idx + LENGTH (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr))))` by
    (irule run_inst_seq_gas_path_mem >> simp[] >>
     conj_tac >- simp[abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def] >>
     conj_tac >- simp[DROP_LENGTH_APPEND, abi_decode_backedge_insts_def] >>
     irule abi_decode_backedge_prefix_mem_ok >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s _ (OK t)` >>
  `gas_path_mem ctx fn t 0 (OK (jump_to hdr t))` by
    (irule for_range_jump_at_zero_path_mem >>
     conj_tac >- simp[Abbr `t`, mstore_def, write_memory_with_expansion_def, update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+2) JMP [Label hdr] []`] >>
     simp[Abbr `t`, abi_decode_backedge_insts_def, get_instruction_def,
          EL_APPEND_EQN, mstore_def, write_memory_with_expansion_def, update_var_def,
          mk_inst_def, is_terminator_def, inst_dload_in_section_def,
          below_frontier_no_ranges, step_inst_base_opcode_eqs]) >>
  drule_all gas_path_mem_then >>
  simp[Abbr `t`, abi_decode_backedge_insts_def, mk_inst_def, jump_to_def]
QED

Theorem abi_decode_position_header_resources:
  let t = jump_to lbl (abi_decode_position_header_state base_op first B sb i ncount s) in
  alloca_inv s /\ alloca_room ctx fn s /\ alloca_history fn s ==>
  alloca_inv t /\ alloca_room ctx fn t /\ alloca_history fn t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_memory = s.vs_memory /\
  (!op. abi_decoder_operand_live first op ==> eval_operand op t = eval_operand op s)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `!op. abi_decoder_operand_live first op ==>
    eval_operand op (jump_to lbl
      (abi_decode_position_header_state base_op first B sb i ncount s)) = eval_operand op s` by
    (Cases >> simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, eval_operand_def, jump_to_def] >>
     Cases_on `base_op = Lit 0w` >>
     simp[jump_to_def, abi_decode_position_header_state_def,
          abi_decode_position_header_delta_def, lookup_var_update_var, update_var_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  `(jump_to lbl (abi_decode_position_header_state base_op first B sb i ncount s)).vs_allocas = s.vs_allocas /\
       (jump_to lbl (abi_decode_position_header_state base_op first B sb i ncount s)).vs_alloca_next = s.vs_alloca_next /\
       (jump_to lbl (abi_decode_position_header_state base_op first B sb i ncount s)).vs_inst_idx = 0 /\
       (jump_to lbl (abi_decode_position_header_state base_op first B sb i ncount s)).vs_memory = s.vs_memory` by
    (Cases_on `base_op = Lit 0w` >>
     simp[jump_to_def, abi_decode_position_header_state_def, update_var_def]) >>
  metis_tac[alloca_inv_fields, alloca_room_fields, alloca_history_jump]
QED

Theorem abi_decode_backedge_resources:
  let t = jump_to hdr (mstore (w2n (p:bytes32)) w (update_var nv w s)) in
  alloca_inv s /\ alloca_room ctx fn s /\ alloca_history fn s ==>
  alloca_inv t /\ alloca_room ctx fn t /\ alloca_history fn t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  mload (w2n p) t = w /\ abi_decode_frame (w2n p) 32 s t /\
  (!op. op <> Var nv ==> eval_operand op t = eval_operand op s)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `!op. op <> Var nv ==>
    eval_operand op (jump_to hdr (mstore (w2n p) w (update_var nv w s))) = eval_operand op s` by
    (Cases >> simp[jump_to_def, eval_operand_mstore, eval_operand_def, lookup_var_update_var]) >>
  `abi_decode_frame (w2n p) 32 s
    (jump_to hdr (mstore (w2n p) w (update_var nv w s)))` by
    (mp_tac (Q.INST [`d` |-> `w2n (p:bytes32)`] abiDecoderArrayHeaderTheory.abi_decode_mstore_frame) >>
     simp[abi_decode_frame_def, jump_to_def, mstore_def, update_var_def]) >>
  `mload (w2n p) (jump_to hdr (mstore (w2n p) w (update_var nv w s))) = w` by
    metis_tac[abi_decode_backedge_observations, listTheory.MEM] >>
  `(jump_to hdr (mstore (w2n p) w (update_var nv w s))).vs_allocas = s.vs_allocas /\
    (jump_to hdr (mstore (w2n p) w (update_var nv w s))).vs_alloca_next = s.vs_alloca_next /\
    (jump_to hdr (mstore (w2n p) w (update_var nv w s))).vs_inst_idx = 0` by
    simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  metis_tac[alloca_inv_fields, alloca_room_fields, alloca_history_jump]
QED
