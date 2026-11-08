(* Canonical primitive decoder endpoints, with actual execution observations. *)
Theory entryReachBodyCanonicalWordEndpoint
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyRecursiveInterface entryReachBodyOperationalPath
  entryReachBodySequenceObservations entryReachBodyExactArrayLoop abiDecoderPrimitiveMemory
  abiDecoderClampedWord abiDecoderWordTyped abiEncoder ctorAbiActualAlloc abiDecoderContract
  abiEncoderRegisteredEffect entryReachBodyOwnedRegion entryReachBodyScratchSet
  abiAllocationHistory allocaFrontierBound allocaBudgetProps venomMemDefs
  venomExecSemantics venomInstProps venomState venomInst emitHelperProps exprLoweringProps
  compileEnv emitHelper words list rich_list arithmetic

Theorem word_opcode_fields[local]:
  MEM i.inst_opcode [CALLDATALOAD; SIGNEXTEND; EQ; SHR; SHL; ISZERO; ASSERT; MSTORE] /\
  step_inst_base i s = OK t ==> entry_loop_fields s t
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_write2_def, exec_pure2_def, exec_pure1_def, AllCaseEqs()] >> strip_tac >>
  gvs[entry_loop_fields_def, update_var_def, mstore_def,
      write_memory_with_expansion_def]
QED

Theorem word_sequence_fields[local]:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode
    [CALLDATALOAD; SIGNEXTEND; EQ; SHR; SHL; ISZERO; ASSERT; MSTORE]) code ==>
  entry_loop_fields s t
Proof
  strip_tac >> simp[entry_loop_fields_def] >> rpt conj_tac >>
  irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `MEM i.inst_opcode [CALLDATALOAD; SIGNEXTEND; EQ; SHR; SHL; ISZERO; ASSERT; MSTORE]` by
    fs[EVERY_MEM] >>
  drule_all word_opcode_fields >> simp[entry_loop_fields_def]
QED

Theorem word_opcode_shape[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD hi (DecPrimWord clamp) st = ((),last) ==>
  EVERY (\i. MEM i.inst_opcode
    [CALLDATALOAD; SIGNEXTEND; EQ; SHR; SHL; ISZERO; ASSERT; MSTORE])
    (emitted_insts st last)
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem word_registered_frame[local]:
  abi_decode_frame d 32 s t /\ entry_loop_fields s t /\
  t.vs_allocas = s.vs_allocas ==>
  abi_encoder_registered_effect ids [(d,32)] s t
Proof
  simp[abi_decode_frame_def, entry_loop_fields_def,
       abi_encoder_registered_effect_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem word_allocation_invariants[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\
  alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d sz s /\ entry_scratch_ready sites b cap s ==>
  alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\
  alloca_frontier_inv ctx fn site t /\
  entry_owned_region oid root extent d sz t /\ entry_scratch_ready sites b cap t
Proof
  strip_tac >>
  `entry_scratch_ready sites b cap t` by metis_tac[entry_scratch_ready_frame] >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      abi_alloca_history_def, alloca_frontier_inv_def,
      remaining_alloca_budget_def, entry_owned_region_def] >> metis_tac[]
QED

Theorem entry_canonical_word_owned_endpoint:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv (DecPrimWord clamp) av v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce ty) s /\
  entry_scratch_ready sites b cap s ==>
  ?t. val_in_memory tv v d t.vs_memory /\ entry_decode_path ctx fn s t /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\ entry_scratch_ready sites b cap t /\
    alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_bytes ce ty) t /\
    abi_encoder_registered_effect child_sites [(d,type_memory_bytes ce ty)] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_primitive_memory_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st last) s = OK actual` >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `entry_loop_fields s actual` by
    (irule word_sequence_fields >> goal_assum (drule_at Any) >>
     irule word_opcode_shape >> goal_assum (drule_at Any)) >>
  `entry_decode_path ctx fn s (actual with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule entry_decode_emitted_path >> goal_assum (drule_at Any) >>
     simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `type_memory_bytes ce ty = 32` by
    (drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >> simp[]) >>
  `abi_encoder_registered_effect child_sites [(d,32)] s actual` by
    (irule word_registered_frame >> simp[]) >>
  `actual.vs_current_bb = s.vs_current_bb` by
    (irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
     rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all step_preserves_control_flow >> simp[]) >>
  `alloca_inv (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   abi_alloca_history (fn_insts fn) (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   alloca_frontier_inv ctx fn site (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   entry_owned_region oid root extent d (type_memory_bytes ce ty)
     (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   entry_scratch_ready sites b cap (actual with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule word_allocation_invariants >> qexists_tac `s` >> simp[]) >>
  qexists_tac `actual with vs_inst_idx := LENGTH last.cs_current_insts` >>
  gvs[fresh_vars_wrt_def, entry_loop_fields_def, abi_encoder_registered_effect_def,
       eval_operand_def] >> first_assum ACCEPT_TAC
QED
