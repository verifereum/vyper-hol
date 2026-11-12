(* Memory checks and real-state transport for decoder reentry. *)
Theory abiDecodeMemReentry
Ancestors
  abiDecoderVarExtend abiDecoderVarSequence abiDecoderReentry fragGasPathMem fragGasSeqMem
  execEquivParamProps execEquivParamDefs codegenRel contextCodegenRel memSafeRun unitTransformDefs
  abiEncoderVarTransport opcodeClass venomExecSemantics venomState venomInst finite_map list

Theorem abi_decode_reentry_operand_agreement:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  Cases >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem abi_decode_reentry_memory_checks:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode ==>
  (inst_mem_below_frontier inst s <=> inst_mem_below_frontier inst t) /\
  (inst_dload_in_section inst s <=> inst_dload_in_section inst t)
Proof
  strip_tac >> drule abi_decode_reentry_operand_agreement >> disch_then drule >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def, inst_dload_in_section_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> fs[fixed_source_write_range_def, sized_source_write_range_def] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> fs[fixed_source_write_range_def, sized_source_write_range_def] >>
  rename1 `h::h'::h''::rest` >> Cases_on `rest` >> fs[fixed_source_write_range_def, sized_source_write_range_def] >>
  fs[fixed_source_write_range_def, sized_source_write_range_def]
QED

Theorem abi_decode_reentry_revert:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v /\
      abi_decoder_vars_extend extras u v
Proof
  strip_tac >>
  `inst.inst_opcode = ASSERT` by
    (drule opcodeClassTheory.step_inst_base_abort_opcodes >>
     fs[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  drule abi_decode_reentry_operand_agreement >> disch_then drule >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[step_inst_base_def] >>
  simp[abi_decoder_vars_extend_def, vsr_frame_def, abi_decoder_var_map_def,
    revert_state_def, set_returndata_def, Excl "vsr_complete_mask_equality"] >>
  fs[abi_decoder_vars_extend_def, vsr_frame_def, abi_decoder_var_map_def,
     Excl "vsr_complete_mask_equality"] >>
  qpat_x_assum `s with vs_vars := FEMPTY = _`
    (mp_tac o Q.AP_TERM `\u:venom_state. u with <|vs_returndata := []; vs_halted := T|>`) >> simp[]
QED


Theorem abi_decode_reentry_edge_check[local]:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) ==>
  (revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t)
Proof
  strip_tac >> drule_all abi_encoder_vars_extend_control >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[abi_decoder_reentry_non_invoke] >>
  drule_all abi_decode_reentry_memory_checks >> strip_tac >>
  fs[mem_safe_step_non_invoke]
QED

Theorem abi_decode_reentry_edge_next:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK u ==>
  ?v. gas_path_mem_edge ctx fn t 0 (OK v) /\
      abi_decoder_vars_extend extras (u with vs_inst_idx := SUC s.vs_inst_idx) v
Proof
  strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  `revert_forward_at bb t.vs_inst_idx \/ mem_safe_step 0 ctx inst t`
    by (irule abi_decode_reentry_edge_check >> simp[] >> metis_tac[]) >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  rename1 `step_inst_base inst t = OK large` >>
  drule_all abi_encoder_vars_extend_control >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    fs[abi_decoder_reentry_opcode_def] >>
  `~large.vs_halted` by metis_tac[venomInstProofsTheory.step_preserves_halted,
    step_inst_non_invoke] >>
  qexists_tac `large with vs_inst_idx := SUC s.vs_inst_idx` >>
  reverse conj_tac >- (metis_tac[abi_encoder_vars_extend_idx]) >>
  fs[] >> simp[gas_path_mem_edge_def, step_inst_non_invoke,
    gasCountTheory.gas_count_step_def] >>
  metis_tac[abi_encoder_vars_extend_idx]
QED
