(* Physical dynamic-array loop control, stopping at target entry edges. *)
Theory extcallDecoderLoopEdgesMemory
Ancestors
  extcallDecoderHeaderMemory abiDecoderExecution abiDecoderContract
  fragGasSeqMem fragGasPathMem stmtForRangeMemoryParts
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
