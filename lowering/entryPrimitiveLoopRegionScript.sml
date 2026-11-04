(* Control confinement of the actual primitive-element decoder loop. *)
Theory entryPrimitiveLoopRegion
Ancestors
  abiDecoderPrimitiveLoopLayout abiDecoderPrimitiveLoopContext
  abiDecoderPrimitiveLoopInvariant abiDecoderLoopCode abiEncoderObserver
  abiDecoderLoopEmit abiDecoderPrimitiveLoopFragment abiDecoderExecution
  abiDecoderContract exprLoweringProps
  fragExec emitHelperProps compileEnv venomInstProofs venomExecProofs
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem entry_loop_header_control[local]:
  abi_decode_loop_cfg fn h b e id ip src CALLDATALOAD iv cv cmp done /\
  abi_observer_step ctx fn (e,0) s t /\ s.vs_current_bb = h ==>
  t.vs_current_bb = h \/ t.vs_current_bb = b \/
  (t.vs_current_bb = e /\ t.vs_inst_idx = 0)
Proof
  rw[abi_decode_loop_cfg_def, abi_observer_step_def] >>
  gvs[get_instruction_def, abi_decode_header_insts_def]
  >- (drule_all step_preserves_control_flow >> simp[]) >>
  `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1 \/ s.vs_inst_idx = 2 \/
   s.vs_inst_idx = 3 \/ s.vs_inst_idx = 4` by decide_tac >>
  gvs[mk_inst_def, is_terminator_def] >>
  gvs[mk_inst_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      AllCaseEqs(), jump_to_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[]
QED

Theorem entry_loop_body_control[local]:
  lookup_block b fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip h /\
  EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
  abi_observer_step ctx fn cut s t /\ s.vs_current_bb = b ==>
  t.vs_current_bb = b \/ t.vs_current_bb = h
Proof
  rw[abi_observer_step_def]
  >- (drule_all step_preserves_control_flow >> simp[]) >>
  gvs[get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH prefix`
  >- (gvs[EL_APPEND_EQN] >>
      fs[EVERY_EL] >> metis_tac[]) >>
  gvs[EL_APPEND_EQN, abi_decode_backedge_insts_def] >>
  `s.vs_inst_idx - LENGTH prefix = 0 \/
   s.vs_inst_idx - LENGTH prefix = 1 \/
   s.vs_inst_idx - LENGTH prefix = 2` by decide_tac >>
  gvs[mk_inst_def, is_terminator_def, step_inst_non_invoke,
      step_inst_base_opcode_eqs, jump_to_def] >>
  drule eval_phis_preserves_current_bb >> simp[]
QED

Theorem entry_primitive_compiled_region[local]:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst
    CALLDATALOAD hi clamp h e hid first iv limit_st /\
  EVERY (\i. ~is_terminator i.inst_opcode) st1.cs_current_insts ==>
  observer_region_closed ctx fn (e,0)
    {p | FST p = h \/ FST p = st0.cs_current_bb \/ p = (e,0)}
Proof
  simp_tac bool_ss [abi_decoder_primitive_loop_compiled_def,
    abi_decoder_primitive_loop_code_def] >> strip_tac >>
  rw[observer_region_closed_def] >> gvs[]
  >- metis_tac[entry_loop_header_control]
  >- metis_tac[entry_loop_body_control] >>
  gvs[abi_observer_step_def]
QED

Theorem entry_primitive_loop_region_closed:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD hi (DecPrimWord clamp)
    32 32 ip cnt start = ((),end_st) /\
  fn_has_code start end_st fn /\
  h = fresh_label_output "dec_dyn_hdr" start.cs_next_label /\
  b = fresh_label_output "dec_dyn_body" (start.cs_next_label + 1) /\
  e = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
  h <> b /\ h <> e /\ b <> e /\
  (!bb. lookup_block e fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  observer_region_closed ctx fn (e,0)
    {p | FST p = h \/ FST p = b \/ p = (e,0)}
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `st0.cs_current_insts = []` by
    gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) st1.cs_current_insts` by
    gvs[emitted_insts_def, EVERY_CONJ] >>
  drule_all abi_decoder_primitive_setup_head >> strip_tac >>
  `end_st.cs_current_bb = e` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
     gvs[abi_decode_loop_suffix_state_def, abi_decode_loop_prefix_shape]) >>
  `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule_all abi_decoder_primitive_loop_layout >> strip_tac >>
  drule_all entry_primitive_compiled_region >>
  gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def]
QED
