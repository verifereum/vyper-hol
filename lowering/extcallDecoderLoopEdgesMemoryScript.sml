(* Physical dynamic-array loop control, stopping at target entry edges. *)
Theory extcallDecoderLoopEdgesMemory
Ancestors
  extcallDecoderHeaderMemory abiDecoderExecution abiDecoderContract
  abiEncoderArrayRound abiScratchEffect abiDecoderArrayBackedge
  fragGasSeqMem fragGasPathMem fragExecMem stmtForRangeMemoryParts
  instMemFrontier memSafeRun venomInstProofs venomExecSemantics venomState
  venomInst words arithmetic list rich_list

Theorem extcall_decoder_header_prefix_path[local]:
  abi_decode_position_loop_ready hdr ip src MLOAD base_op B sb p c j s /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  B+sb < dimword(:256) /\ c < dimword(:256) /\
  w2n p+32 <= s.vs_alloca_next /\ B+sb+32 <= s.vs_alloca_next /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl|> ==>
  gas_path_mem ctx func s 0
    (OK ((abi_decode_position_header_state base_op first B sb j c s) with
      vs_inst_idx := LENGTH (FRONT
        (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))))
Proof
  strip_tac >>
  drule_all extcall_decoder_header_prefix_mem_ok >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq
     (FRONT (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl)) s =
     OK (abi_decode_position_header_state base_op first B sb j c s)` by
    (`run_inst_seq
       (TAKE (4 + abi_decode_position_header_delta base_op)
         (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl)) s =
       OK (abi_decode_position_header_state base_op first B sb j c s)` by
       (irule abi_decode_position_header_prefix >>
        gvs[abi_decode_position_loop_ready_def] >> metis_tac[]) >>
     Cases_on `base_op = Lit 0w` >>
     gvs[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (FRONT (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl)) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS)
     (FRONT (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))) = 0` by
    (Cases_on `base_op = Lit 0w` >>
     simp[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def,
          mk_inst_def, is_terminator_def]) >>
  fs[abi_decode_position_loop_ready_def] >>
  `isPREFIX
     (FRONT (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))
     (DROP s.vs_inst_idx
       (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl))` by
    (Cases_on `base_op = Lit 0w` >>
     simp[abi_decode_position_header_insts_def, abi_decode_position_header_delta_def]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`,
    `<|bb_label := hdr; bb_instructions :=
       abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl|>`] mp_tac) >>
  gvs[]
QED

Theorem extcall_decoder_header_path:
  abi_decode_position_loop_ready hdr ip src MLOAD base_op B sb p c j s /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  B+sb < dimword(:256) /\ c < dimword(:256) /\
  w2n p+32 <= s.vs_alloca_next /\ B+sb+32 <= s.vs_alloca_next /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl|> ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if j<c then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B sb j c s)))
Proof
  strip_tac >> drule_all extcall_decoder_header_prefix_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK u)` >>
  `gas_path_mem ctx func u 0
     (OK (jump_to (if j<c then body_lbl else exit_lbl) u))` by
    (irule for_range_jump_at_zero_path_mem >>
     conj_tac >- (Cases_on `base_op = Lit 0w` >>
       gvs[Abbr `u`, abi_decode_position_header_state_def,
           update_var_def, abi_decode_position_loop_ready_def]) >>
     qexistsl
       [`<|bb_label := hdr; bb_instructions :=
           abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl|>`,
        `LAST (abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl)`] >>
     Cases_on `base_op = Lit 0w` >>
     gvs[Abbr `u`, abi_decode_position_loop_ready_def,
         abi_decode_position_header_insts_def, abi_decode_position_header_delta_def,
         abi_decode_position_header_state_def, update_var_def,
         get_instruction_def, mk_inst_def, is_terminator_def,
         inst_dload_in_section_def, below_frontier_no_ranges] >>
     simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `j<c` >> simp[bool_to_word_def]) >>
  `jump_to (if j<c then body_lbl else exit_lbl) u =
   jump_to (if j<c then body_lbl else exit_lbl)
     (abi_decode_position_header_state base_op first B sb j c s)` by
    simp[Abbr `u`, jump_to_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Theorem extcall_decoder_increment_mem_ok[local]:
  eval_operand ip s = SOME p /\ ip <> Var nv /\
  w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s
Proof
  strip_tac >>
  `!w. eval_operand ip (update_var nv w s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
                         finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[abi_decode_backedge_insts_def, run_inst_seq_mem_ok_def,
       mk_inst_def, below_frontier_no_ranges, inst_dload_in_section_def] >>
  Cases_on `eval_operand (Var iv) s` >>
  simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, GSYM update_var_def] >>
  simp[below_frontier_MSTORE, exec_write2_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[update_var_def]
QED

Theorem extcall_decoder_backedge_prefix_path[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ j < c /\ c < dimword(:256) /\
  w2n p+32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK ((mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s))
      with vs_inst_idx := LENGTH prefix + 2))
Proof
  strip_tac >> drule_all abi_decode_increment_prefix >>
  disch_then (qspecl_then [`id`, `hdr`] assume_tac) >>
  drule_all extcall_decoder_increment_mem_ok >>
  disch_then (qspecl_then [`iv`, `id`, `hdr`] assume_tac) >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  gvs[abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def,
      DROP_LENGTH_APPEND]
QED

Theorem extcall_decoder_backedge_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ j < c /\ c < dimword(:256) /\
  w2n p+32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) s))))
Proof
  strip_tac >> drule_all extcall_decoder_backedge_prefix_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK u)` >>
  `gas_path_mem ctx func u 0 (OK (jump_to hdr u))` by
    (irule for_range_jump_at_zero_path_mem >>
     conj_tac >- gvs[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def] >>
     qexistsl [`bb`, `mk_inst (id+2) JMP [Label hdr] []`] >>
     gvs[Abbr `u`, mstore_def, write_memory_with_expansion_def, update_var_def,
         get_instruction_def, abi_decode_backedge_insts_def, EL_APPEND_EQN,
         mk_inst_def, is_terminator_def, below_frontier_no_ranges,
         inst_dload_in_section_def] >>
     simp[step_inst_base_opcode_eqs]) >>
  `jump_to hdr u = jump_to hdr
      (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s))` by
    simp[Abbr `u`, jump_to_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

(* Registered counter write: the very same raw-entry path carries the
   scratch frame, so source windows and initialized output stay protected. *)
Theorem extcall_decoder_backedge_scratch_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword(:256) /\
  j < c /\ c < dimword(:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  slot+32 <= s.vs_alloca_next /\
  abi_decoder_budget first last b cap s /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  ?actual. gas_path_mem ctx func s 0 (OK actual) /\
    mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\
    abi_scratch_effect first last lo hi next limit_st d sz b cap s actual
Proof
  strip_tac >>
  drule_all abi_encoder_array_backedge_execute >>
  disch_then (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
  `ip <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> metis_tac[LESS_EQ_REFL]) >>
  `gas_path_mem ctx func s 0 (OK actual)` by
    (`w2n (n2w slot:bytes32)+32 <= s.vs_alloca_next` by simp[w2n_n2w] >>
     drule_all extcall_decoder_backedge_path >> simp[w2n_n2w]) >>
  `abi_scratch_effect first last lo hi next limit_st d sz b cap s actual` by
    (irule abi_scratch_single_write >> metis_tac[]) >>
  qexists_tac `actual` >> simp[]
QED
