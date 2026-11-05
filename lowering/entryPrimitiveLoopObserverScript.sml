(* STOP observers for actual primitive decoder loops. *)
Theory entryPrimitiveLoopObserver
Ancestors
  entryPrimitiveLoopRegion abiDecoderPrimitiveLoopLayout abiDecoderPrimitiveLoopContext
  abiDecoderPrimitiveLoopInvariant abiDecoderLoopEmit abiDecoderPrimitiveLoopFragment
  abiDecoderExecution abiDecoderContract abiEncoderObserver exprLoweringProps
  fragExec emitHelperProps compileEnv venomExecProofs venomInstProofs opcodeClass
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem entry_loop_instruction_safe[local]:
  inst.inst_opcode <> INVOKE /\
  (~is_terminator inst.inst_opcode \/ inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) ==>
  (!s h. ~s.vs_halted ==> step_inst_base inst s <> Halt h) /\
  (!s middle. ~s.vs_halted /\ step_inst_base inst s = OK middle ==> ~middle.vs_halted)
Proof
  disch_tac >> conj_tac
  >- (rpt strip_tac >> drule step_inst_base_halt_opcodes >> strip_tac >>
      gvs[is_terminator_def]) >>
  rpt strip_tac >> drule venomExecProofsTheory.step_inst_base_OK_preserves_halted >> simp[]
QED

Theorem entry_primitive_compiled_safe[local]:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst
    CALLDATALOAD hi clamp h e hid first iv limit_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    st1.cs_current_insts /\
  lookup_block e fn.fn_blocks = SOME exit_bb /\
  get_instruction exit_bb 0 = SOME (mk_inst stop_id STOP [] []) ==>
  observer_region_safe fn (e,0)
    {p | FST p = h \/ FST p = st0.cs_current_bb \/ p = (e,0)}
Proof
  simp_tac bool_ss [abi_decoder_primitive_loop_compiled_def,
    abi_decoder_primitive_loop_code_def, abi_decode_loop_cfg_def] >> strip_tac >>
  simp_tac bool_ss [observer_region_safe_def, pairTheory.FST, pairTheory.SND] >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  map_every qx_gen_tac [`lbl`, `idx`, `code_bb`, `inst`] >> strip_tac >>
  `MEM inst code_bb.bb_instructions` by
    (qpat_x_assum `get_instruction code_bb idx = SOME inst` mp_tac >>
     simp[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> INVOKE /\
    (~is_terminator inst.inst_opcode \/ inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ)` by
    (gvs[abi_decode_header_insts_def, abi_decode_backedge_insts_def,
         MEM_APPEND, mk_inst_def, EVERY_MEM] >>
     metis_tac[is_terminator_def]) >>
  simp[] >> irule entry_loop_instruction_safe >> simp[]
QED

Theorem entry_primitive_loop_observer_safe:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD hi (DecPrimWord clamp)
    32 32 ip cnt start = ((),end_st) /\
  fn_has_code start end_st fn /\
  h = fresh_label_output "dec_dyn_hdr" start.cs_next_label /\
  b = fresh_label_output "dec_dyn_body" (start.cs_next_label + 1) /\
  e = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
  h <> b /\ h <> e /\ b <> e /\
  (!bb. lookup_block e fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  lookup_block e fn.fn_blocks = SOME exit_bb /\
  get_instruction exit_bb 0 = SOME (mk_inst stop_id STOP [] []) ==>
  observer_region_safe fn (e,0)
    {p | FST p = h \/ FST p = b \/ p = (e,0)}
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `st0.cs_current_insts = []` by
    gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    st1.cs_current_insts` by gvs[emitted_insts_def] >>
  drule_all abi_decoder_primitive_setup_head >> strip_tac >>
  `end_st.cs_current_bb = e` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
     gvs[abi_decode_loop_suffix_state_def, abi_decode_loop_prefix_shape]) >>
  `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule_all abi_decoder_primitive_loop_layout >> strip_tac >>
  `FST labels = h /\ SND (SND labels) = e /\ st0.cs_current_bb = b` by
    gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
  fs[] >> drule_all entry_primitive_compiled_safe >> simp[]
QED

Theorem entry_primitive_loop_run_prefix:
  compile_abi_decode_dyn_loop dst src CALLDATALOAD hi (DecPrimWord clamp)
    32 32 ip cnt start = ((),end_st) /\
  fn_has_code start end_st fn /\
  h = fresh_label_output "dec_dyn_hdr" start.cs_next_label /\
  b = fresh_label_output "dec_dyn_body" (start.cs_next_label + 1) /\
  e = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
  h <> b /\ h <> e /\ b <> e /\
  (!bb. lookup_block e fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  lookup_block e fn.fn_blocks = SOME exit_bb /\
  get_instruction exit_bb 0 = SOME (mk_inst stop_id STOP [] []) /\
  (s.vs_current_bb = h \/ s.vs_current_bb = b \/
   (s.vs_current_bb = e /\ s.vs_inst_idx = 0)) /\
  ~s.vs_halted /\ run_from fuel ctx fn s = Halt result ==>
  ?u. local_prefix ctx fn (e,0) s u /\ stop_view u = result
Proof
  strip_tac >> (
  drule_all entry_primitive_loop_observer_safe >> strip_tac >>
  drule_all entry_primitive_loop_region_closed >> strip_tac >>
  irule observer_region_run_prefix >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `fuel` >> simp[]) >>
  qexists_tac `{p | FST p = h \/ FST p = b \/ p = (e,0)}` >> simp[])
QED
