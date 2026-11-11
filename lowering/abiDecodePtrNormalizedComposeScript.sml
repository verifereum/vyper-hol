Theory abiDecodePtrNormalizedCompose
Ancestors
  abiDecodePtrEntry abiDecodePtrNormalizedSuccess abiDecodePtrComplexOutcomeAbort
  abiDecodePtrMemberInterface abiDecoderReentry abiDecoderAppend
  abiDecodePtrRejectChecks abiDecoderVarSequence
  bodyPtrBopScalarSeq exprLoweringProps emitHelperProps fragExec instIdxIndep
  compileEnv venomState venomExecSemantics list arithmetic
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  context emitHelper venomInst rich_list loweringHalt

Theorem abi_decode_header_reentry_code:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sh)
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_setup_code:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) ==>
  inst_extends sa ready /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts sa ready)
Proof
  strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_decode_header_reentry_code >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `inst_extends sh ready` by simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `inst_extends sa ready` by
    (irule inst_extends_trans >> qexists_tac `sh` >> simp[]) >>
  `emitted_insts sa ready = emitted_insts sa sh ++ emitted_insts sh ready` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  fs[EVERY_CONJ] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def,
    abi_decoder_reentry_opcode_def, is_terminator_def]
QED

Theorem abi_decode_setup_success_sequence:
  run_inst_seq (emitted_insts sa ready) (abi_decoder_prune_vars sa.cs_next_var s) =
    OK (u0 with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa ready)
    (abi_decoder_prune_vars sa.cs_next_var s) H tf /\
  inst_extends sa ready /\ inst_extends ready sb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa ready) /\
  abi_decode_member_live ret ctx func cenv cx es src b (LENGTH bs) dst d cap
    (Lit 0w) 0w hi ready H tf u0 /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys [BytesV bs] =
    INL (ArrayV (TupleV vs)) /\
  LIST_REL value_has_type tvs vs /\ LIST_REL val_wf tvs vs /\
  mem_bytes_at (w2n b) (LENGTH bs) (abi_decode_source MLOAD u0) = bs /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) ready = ((),sb) /\
  fn_has_code ready sb func ==>
  ?u K tk.
    run_inst_seq (emitted_insts sa sb) (abi_decoder_prune_vars sa.cs_next_var s) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
      (abi_decoder_prune_vars sa.cs_next_var s) K tk /\
    abi_decode_member_live ret ctx func cenv cx es src b (LENGTH bs) dst d cap
      (Lit 0w) 0w hi sb K tk u /\
    (!mem'. mem_agree_outside tk.t_mem u.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d) mem') /\
    abi_decode_member_frame ready H tf u0 K tk u (w2n d) cap
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule_all abi_decode_normalized_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `emitted_insts sa sb = emitted_insts sa ready ++ emitted_insts ready sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `(abi_decoder_prune_vars sa.cs_next_var s).vs_inst_idx +
     LENGTH (emitted_insts sa ready) = u0.vs_inst_idx` by
    (fs[abi_decoder_prune_vars_def, inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  suspend "compose"
QED

Resume abi_decode_setup_success_sequence[compose]:
  markerLib.RESUME_TAC >>
  `run_inst_seq (emitted_insts ready sb) (u0 with vs_inst_idx := s.vs_inst_idx) =
     OK (u with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `run_inst_seq (emitted_insts sa sb) (abi_decoder_prune_vars sa.cs_next_var s) =
     OK (u with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `run_inst_seq (emitted_insts sa ready) _ = _`
       (mp_then Any (qspec_then `emitted_insts ready sb` mp_tac) run_inst_seq_append) >>
     simp[]) >>
  `u0 with vs_inst_idx := LENGTH ready.cs_current_insts = u0` by
    (simp_tac (srw_ss()) [NoAsms, venom_state_component_equality] >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG H tf (emitted_insts ready sb)
     ((u0 with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx :=
       (abi_decoder_prune_vars sa.cs_next_var s).vs_inst_idx +
        LENGTH (emitted_insts sa ready)) H' tf'` by simp[] >>
  drule_all bop_inst_seq_ptr_append >> strip_tac >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `H'`, `tf'`] >>
  simp[]
QED

Finalise abi_decode_setup_success_sequence

Theorem abi_decode_reject_witness_inst_idx:
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  abi_decode_reject_witness code s u ==>
  abi_decode_reject_witness code (s with vs_inst_idx := n) (u with vs_inst_idx := n)
Proof
  rw[abi_decode_reject_witness_def] >>
  qexistsl_tac [`pre`, `bad`, `post`, `r with vs_inst_idx := n`] >>
  gvs[run_inst_seq_inst_idx, step_inst_inst_idx_indep, exec_result_map_def,
    abi_decoder_inputs_defined_def, eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_setup_reject_sequence:
  run_inst_seq (emitted_insts sa ready) (abi_decoder_prune_vars sa.cs_next_var s) =
    OK (u0 with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa ready)
    (abi_decoder_prune_vars sa.cs_next_var s) H tf /\
  inst_extends sa ready /\ inst_extends ready sb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa ready) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa ready) /\
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap
    (Lit 0w) 0w hi ready H tf u0 /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) ready = ((),sb) /\
  fn_has_code ready sb func /\
  abi_decode_reject_witness (emitted_insts ready sb) u0 u ==>
  ?K tk. run_inst_seq (emitted_insts sa sb) (abi_decoder_prune_vars sa.cs_next_var s) =
      Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
      (abi_decoder_prune_vars sa.cs_next_var s) K tk /\
    abi_decode_reject_witness (emitted_insts sa sb)
      (abi_decoder_prune_vars sa.cs_next_var s) (u with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_reject_witness_run >> strip_tac >>
  drule_all abi_decode_complex_observed_abort >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `emitted_insts sa sb = emitted_insts sa ready ++ emitted_insts ready sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `(abi_decoder_prune_vars sa.cs_next_var s).vs_inst_idx +
     LENGTH (emitted_insts sa ready) = u0.vs_inst_idx` by
    (fs[abi_decoder_prune_vars_def, inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  `abi_decode_reject_witness (emitted_insts ready sb)
     (u0 with vs_inst_idx := s.vs_inst_idx) (u with vs_inst_idx := s.vs_inst_idx)` by
    (irule abi_decode_reject_witness_inst_idx >> simp[]) >>
  `abi_decode_reject_witness (emitted_insts sa sb)
     (abi_decoder_prune_vars sa.cs_next_var s) (u with vs_inst_idx := s.vs_inst_idx)` by
    (simp[] >> irule abi_decode_reject_witness_prefix >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sb) (abi_decoder_prune_vars sa.cs_next_var s) =
     Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx)` by
    metis_tac[abi_decode_reject_witness_run] >>
  `u0 with vs_inst_idx := LENGTH ready.cs_current_insts = u0` by
    (simp_tac (srw_ss()) [NoAsms, venom_state_component_equality] >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG H tf (emitted_insts ready sb)
     ((u0 with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx :=
       (abi_decoder_prune_vars sa.cs_next_var s).vs_inst_idx +
        LENGTH (emitted_insts sa ready)) H' tf'` by simp[] >>
  drule_all bop_inst_seq_ptr_append >> metis_tac[]
QED
