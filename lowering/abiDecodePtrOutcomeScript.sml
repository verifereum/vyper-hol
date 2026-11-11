(* Actual-start paths obtained from normalized whole-interval certificates. *)
Theory abiDecodePtrOutcome
Ancestors
  abiDecodePtrRejectSequence abiDecodePtrReentry abiDecoderVarExtend
  abiDecodePtrRejectChecks abiDecoderVarSequence exprSimProps
  abiDecodePtrMemberInterface abiDecodePtrObservationTransport abiDecodePtrReentryObservations
  abiDecodePtrComplexHeader abiDecodePtrFlatLayout abiDecodePtrRejectCode
  abiEncoder emitHelper context abiDecodePtrNormalizedCompose abiDecoderMemberInfos
  abiDecodePtrEntry exprSimHash abiDecoderContract
  words arithmetic abiDecoderReentry abiBuiltinDecodeHeader loweringHalt execEquivParamDefs
  fragGasSeqPtr stmtReasonLitFragMemory exprLoweringProps fragExec emitHelperProps compileEnv venomExecSemantics
  venomState venomInst list rich_list

Theorem abi_decode_actual_reject_path:
  fn_has_code sa sb func /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  abi_decoder_vars_extend extras r s /\
  abi_decode_reject_witness (emitted_insts sa sb) r u /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) r H tf ==>
  ?v n j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort v /\
    vsr_term_frame u = vsr_term_frame v /\
    gas_path_ptr D lo ctx func PG G tn s n H tf
      (Abort Revert_abort (v with vs_inst_idx := j))
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all abi_decode_ptr_reject_sequence_extend >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[] >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem abi_decode_actual_success_path:
  fn_has_code sa sb func /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  abi_decoder_vars_extend extras r s /\
  run_inst_seq (emitted_insts sa sb) r = OK u /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) r H tf ==>
  ?v. run_inst_seq (emitted_insts sa sb) s = OK v /\
    abi_decoder_vars_extend extras u v /\
    gas_path_ptr D lo ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H tf
      (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule_all abi_decode_ptr_sequence_extend >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> abi_decoder_reentry_opcode _ /\ _`
       drule >> simp[abi_decoder_reentry_opcode_def] >>
     metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    metis_tac[LENGTH_APPEND] >>
  strip_tac >> goal_assum (drule_at Any) >> gvs[]
QED

Theorem abi_decode_actual_stmt_state_rel:
  abi_decoder_vars_extend extras s t /\ stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (drule abi_decoder_vars_extend_restore >>
     simp[venom_state_component_equality]) >>
  pop_assum SUBST1_TAC >> irule stmt_state_rel_vars_frame >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `?w. lookup_var p s = SOME w` by
        (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
      `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
      drule_all abi_decoder_vars_extend_eval >> simp[eval_operand_def, lookup_var_def]) >>
  rpt strip_tac >>
  `eval_operand (Var p) s = SOME 0w` by
    fs[stmt_state_rel_def, immutable_base_zero_def] >>
  drule_all abi_decoder_vars_extend_eval >>
  fs[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_actual_success_post:
  fn_has_code sa sb func /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  abi_decoder_vars_extend extras r s /\
  run_inst_seq (emitted_insts sa sb) r = OK (u with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) r H tf /\
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap
    pos z hi sb H tf u /\
  (!mem'. mem_agree_outside tf.t_mem u.vs_memory mem' ==>
    tuple_in_memory vs tvs (w2n d) mem') ==>
  ?v. gas_path_ptr D lo ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H tf (OK v) /\
    ghost_inv ret cenv cx es H tf v /\ stmt_state_rel ctx func cenv cx es v /\
    lookup_var dst v = SOME d /\ ptr_covers H tf dst v cap /\
    (!mem'. mem_agree_outside tf.t_mem v.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d) mem')
Proof
  strip_tac >>
  drule_all abi_decode_actual_success_path >> strip_tac >>
  `u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    fs[abi_decode_member_live_def] >>
  `abi_decoder_vars_extend extras u (v with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule abi_decode_ptr_reentry_index >>
     disch_then (qspec_then `LENGTH sb.cs_current_insts` mp_tac) >>
     `u with vs_inst_idx := LENGTH sb.cs_current_insts = u` by
       (simp_tac (srw_ss()) [NoAsms, venom_state_component_equality] >> simp[]) >>
     simp[]) >>
  drule abi_decode_member_live_resources >> strip_tac >>
  `ghost_inv ret cenv cx es H tf (v with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule abi_decode_ptr_extend_ghost >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (v with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule abi_decode_actual_stmt_state_rel >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `ptr_covers H tf dst (v with vs_inst_idx := LENGTH sb.cs_current_insts) cap` by
    (irule abi_decode_ptr_extend_covers >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `eval_operand (Var dst) u = SOME d` by simp[eval_operand_def] >>
  drule_all abi_decoder_vars_extend_eval >>
  drule_all abi_decoder_vars_extend_observations >>
  rpt strip_tac >>
  qexists_tac `v with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_complex_header_reentry:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >>
  strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def,
       is_terminator_def]
QED

Theorem abi_decode_complex_reentry_shape:
  hi <> Lit 0w /\ abi_decode_flat_layout infos 0 0 z h cap /\
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecComplex dyn infos) sa = ((),sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  drule_all abi_decode_complex_bounded_split >> strip_tac >>
  rename1 `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ middle = ((),sb)` >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  drule_all abi_decode_complex_header_reentry >> strip_tac >>
  drule_all abi_decode_flat_compile_shape >> strip_tac >>
  drule_all abi_decode_flat_reentry_code >> strip_tac >>
  `inst_extends sa sb` by
    (irule inst_extends_trans >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa middle ++ emitted_insts middle sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  fs[inst_extends_def, same_blocks_def, EVERY_MEM] >> metis_tac[]
QED

Theorem abi_decode_setup_complex_shape:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\ hi <> Lit 0w /\
  abi_decode_flat_layout infos 0 0 z h cap /\
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecComplex dyn infos) ready = ((),sb) ==>
  inst_extends sa ready /\ inst_extends ready sb /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts sa ready) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >>
  drule_all abi_decode_setup_code >> strip_tac >>
  drule_all abi_decode_complex_reentry_shape >> strip_tac >>
  `inst_extends sa sb` by
    (irule inst_extends_trans >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa ready ++ emitted_insts ready sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule abi_builtin_decode_header_shape >> strip_tac >>
     drule compile_alloc_buffer_insts >> simp[]) >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_decode_setup_actual_success:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\
  run_inst_seq (emitted_insts sa ready) (abi_decoder_prune_vars sa.cs_next_var s) =
    OK (u0 with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa ready)
    (abi_decoder_prune_vars sa.cs_next_var s) H tf /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
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
  fn_has_code ready sb func /\ fn_has_code sa sb func ==>
  ?v K tk. gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) K tk (OK v) /\
    ghost_inv ret cenv cx es K tk v /\ stmt_state_rel ctx func cenv cx es v /\
    lookup_var dst v = SOME d /\ ptr_covers K tk dst v cap /\
    (!mem'. mem_agree_outside tk.t_mem v.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d) mem')
Proof
  strip_tac >>
  `hi <> Lit 0w /\ cap < dimword(:256)` by fs[abi_decode_member_live_def] >>
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce tys)
    0 0 0w (32 * LENGTH tys) cap` by
    (irule abi_decode_supported_flat_layout >> simp[]) >>
  drule_all abi_decode_setup_complex_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa ready)` by
    fs[EVERY_MEM] >>
  drule_all abi_decode_setup_success_sequence >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars sa.cs_next_var s) s` by
    simp[abi_decoder_prune_extension] >>
  drule_all abi_decode_actual_success_post >> metis_tac[]
QED

Theorem abi_decode_setup_actual_reject:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\
  run_inst_seq (emitted_insts sa ready) (abi_decoder_prune_vars sa.cs_next_var s) =
    OK (u0 with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa ready)
    (abi_decoder_prune_vars sa.cs_next_var s) H tf /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap
    (Lit 0w) 0w hi ready H tf u0 /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) ready = ((),sb) /\
  fn_has_code ready sb func /\ fn_has_code sa sb func /\
  abi_decode_reject_witness (emitted_insts ready sb) u0 u ==>
  ?v K tk n j. vsr_term_frame u = vsr_term_frame v /\
    gas_path_ptr D 0 ctx func PG G tn s n K tk
      (Abort Revert_abort (v with vs_inst_idx := j))
Proof
  strip_tac >>
  `hi <> Lit 0w /\ cap < dimword(:256)` by fs[abi_decode_member_live_def] >>
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce tys)
    0 0 0w (32 * LENGTH tys) cap` by
    (irule abi_decode_supported_flat_layout >> simp[]) >>
  drule_all abi_decode_setup_complex_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa ready) /\
   EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa ready) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> abi_decoder_reentry_opcode _ /\ _`
       drule >> simp[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  drule_all abi_decode_setup_reject_sequence >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars sa.cs_next_var s) s` by
    simp[abi_decoder_prune_extension] >>
  drule_all abi_decode_actual_reject_path >> strip_tac >>
  gvs[vsr_term_frame_def] >> metis_tac[]
QED

Theorem abi_decode_operand_actual_success:
  expr_post ctx func cenv cx e es0 s0c sa s0 es (BytesV bs) (Var p) s /\
  ptr_val_ok cx (expr_type e) (BytesV bs) (Var p) G tn s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\
  fn_has_code sa ready func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ abi_decoder_operand_live sa.cs_next_var (Var p) /\
  mn <= LENGTH bs /\ LENGTH bs <= mx /\ mx < dimword (:256) /\
  ghost_inv ret cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ outsz < dimword (:256) /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  outsz = SUM (MAP (type_memory_bytes ce) tys) /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys [BytesV bs] =
    INL (ArrayV (TupleV vs)) /\
  LIST_REL value_has_type tvs vs /\ LIST_REL val_wf tvs vs /\
  compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD src len
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) ready = ((),sb) /\
  fn_has_code ready sb func /\ fn_has_code sa sb func ==>
  ?v K tk dst d. buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) K tk (OK v) /\
    ghost_inv ret cenv cx es K tk v /\ stmt_state_rel ctx func cenv cx es v /\
    lookup_var dst v = SOME d /\ ptr_covers K tk dst v outsz /\
    (!mem'. mem_agree_outside tk.t_mem v.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d) mem')
Proof
  strip_tac >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  drule_all abi_decode_ptr_operand_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >>
  `mem_bytes_at (w2n (n2w b + 32w:bytes32)) (LENGTH bs)
      (abi_decode_source MLOAD u) = bs` by
    simp[abi_decode_source_def, word_add_def, w2n_n2w, LESS_MOD] >>
  drule_at (Pat `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_decode_setup_actual_success >> simp[] >>
  metis_tac[]
QED
