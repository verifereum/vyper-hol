(* Finite setup execution without assumptions on unrelated registers. *)
Theory exprSimAbiEncodeSetupOpen
Ancestors
  exprSimAbiEncodeOpenSetup abiBuiltinPrefix abiBuiltinSetupFrames
  abiBuiltinAllocation abiBuiltinEncodeAllocate abiBuiltinEncodeMethod
  abiBuiltinEncodeSetup abiBuiltinEncodeCode abiEncodeWindowBuiltin
  abiEncoderSequence abiDecoderContract compileEnv abiDecoderGuards abiDecoderRange
  abiBuiltinEncodeCorrect abiDecoderFrameCompose abiEncoderWrites venomMemProps abiDecoderArrayHeader
  abiDecoderReentry abiDecoderReentryAddress abiDecoderDynamicLoopSetup
  emitHelperProps exprLoweringProps venomExecSemantics venomExecProofs
  venomState venomInst finite_map words arithmetic list rich_list
  emitHelper exprLowering context abiDecoderVarSequence ctorAbiActualWorld
  ctorAbiActualObservations instIdxIndep abiDecoderLoop abiEncoderExtendSim entrySinkExtraction
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame

Theorem abi_encode_open_register_preserves[local]:
  (!op. abi_decoder_operand_live next op ==>
    eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s)
Proof
  Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem abi_encode_open_alloc_buffer[local]:
  compile_alloc_buffer outsz st = (buf,st') /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  qabbrev_tac `allocated = abi_builtin_allocate_state st.cs_next_id outsz s` >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var)) (n2w p) allocated` >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (gvs[Abbr `t`, Abbr `allocated`, abi_builtin_allocate_state_def] >>
     asm_simp_tac (srw_ss()) [Once step_inst_base_def, exec_alloca_def,
       mk_inst_def, w2n_n2w, eval_operand_def, LET_THM, ADD_COMM]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> simp[Abbr `t`, abi_encode_open_register_preserves] >>
     Cases_on `FLOOKUP s.vs_allocas st.cs_next_id = NONE` >>
     Cases_on `op` >> simp[Abbr `allocated`, abi_builtin_allocate_state_def,
       eval_operand_def, lookup_var_def]) >>
  qexists_tac `t` >> simp[run_inst_seq_def] >>
  gvs[abi_builtin_allocation_frame_def, Abbr `t`, Abbr `allocated`,
    update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    abi_builtin_allocate_state_def]
QED

Theorem abi_encode_open_emit_add[local]:
  emit_op ADD [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (a+b) /\
    abi_decoder_address_frame st.cs_next_var s t /\ inst_extends st st'
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id ADD [lhs;rhs]
      [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (a+b) s)` by
    (irule step_ADD >> simp[]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a+b) s` >>
  simp[run_inst_seq_def, abi_decoder_address_frame_def,
    abi_encode_open_register_preserves, update_var_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_encode_open_allocate_sequence:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) ==>
  ?actual. run_inst_seq (emitted_insts st address_st) initial = OK actual /\
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    inst_extends st address_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `st.cs_next_var <= allocated.cs_next_var` by decide_tac >>
  drule_all abi_encode_open_alloc_buffer >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial allocated_s` >>
  `eval_operand (Lit (n2w data_offset)) allocated_s = SOME (n2w data_offset)` by
    simp[eval_operand_def] >>
  drule_all abi_encode_open_emit_add >> strip_tac >>
  rename1 `abi_decoder_address_frame allocated.cs_next_var allocated_s actual` >>
  `eval_operand buf.buf_operand actual = SOME (n2w p)` by
    (gvs[abi_decoder_address_frame_def] >> first_x_assum irule >> simp[]) >>
  `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual` by
    (irule abi_builtin_allocation_frame_suffix >>
     qexistsl_tac [`allocated_s`, `allocated.cs_next_var`] >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `actual` >> gvs[word_add_n2w]
QED

Theorem abi_encode_open_store_sequence[local]:
  emit_void MSTORE [buf;value_op] st = ((),final) /\
  eval_operand buf s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) ==>
  run_inst_seq (emitted_insts st final) s = OK (mstore p w s) /\ inst_extends st final /\
  mload p (mstore p w s) = w /\ abi_decode_frame p 32 s (mstore p w s) /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore p w s).vs_halted = s.vs_halted /\
  (!op. eval_operand op (mstore p w s) = eval_operand op s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
    exec_write2_def, mk_inst_def, w2n_n2w, abi_decode_mstore_frame,
    mload_mstore_same, eval_operand_mstore]
QED

Theorem abi_encode_open_method_sequence:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    mload (p+32) actual = mid << 224 /\
    abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `eval_operand (Lit 32w) initial = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_encode_open_emit_add >> strip_tac >>
  rename1 `abi_decoder_address_frame st.cs_next_var initial prepared` >>
  `eval_operand method_ptr prepared = SOME (n2w (p+32)) /\
   eval_operand (Lit (mid << 224)) prepared = SOME (mid << 224)` by
    simp[word_add_n2w, eval_operand_def] >>
  drule_all abi_encode_open_store_sequence >> strip_tac >>
  `run_inst_seq (emitted_insts st final) initial = OK (mstore (p+32) (mid << 224) prepared) /\
   inst_extends st final` by
    (drule_all abi_decode_sequence_chain >> simp[]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decode_frame (p+32) 32 initial (mstore (p+32) (mid << 224) prepared)` by
    (irule abi_decode_frame_trans >> qexists_tac `prepared` >> simp[abi_decode_frame_def]) >>
  qexists_tac `mstore (p+32) (mid << 224) prepared` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_open_allocate_opcodes[local]:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st address_st)
Proof
  simp[abi_builtin_encode_allocate_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_encode_open_allocate_reach[local]:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\ fn_has_code st address_st func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    actual.vs_current_bb = address_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH address_st.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_encode_open_allocate_opcodes >> strip_tac >>
  drule_all abi_encode_open_allocate_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st address_st) initial = OK encoded` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `abi_encode_exec_frame func initial encoded` by
    (drule abi_encode_framed_allocate_opcodes >> strip_tac >>
     drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH address_st.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, eval_op_inst_idx]
QED

Theorem abi_encode_open_method_opcodes[local]:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_encode_open_method_reach[local]:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  drule abi_encode_open_method_opcodes >> strip_tac >>
  drule_all abi_encode_open_method_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `abi_encode_exec_frame func initial encoded` by
    (drule abi_encode_framed_method_opcodes >> strip_tac >>
     drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  drule abi_builtin_encode_method_window >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_open_method_setup_reach[local]:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))) /\
  32+32*word_size (maxlen+4) < dimword (:256) /\ p+32 < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+36)) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (32+32*word_size (maxlen+4)) p 32 initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_method_setup_context >> strip_tac >>
  drule abi_builtin_encode_allocate_live >> strip_tac >>
  `st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  drule abi_encode_open_allocate_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial addressed` >>
  drule abi_encode_open_method_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `addressed`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func addressed actual` >>
  `actual.vs_halted = addressed.vs_halted` by simp[] >>
  `eval_operand (FST ops) actual = SOME (n2w p) /\
   eval_operand (SND ops) actual = SOME (n2w (p+36))` by
    (conj_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
    (32+32*word_size (maxlen+4)) p 32 initial actual` by
    (drule_all abi_builtin_encode_setup_frame_compose >> simp[]) >>
  `abi_encode_exec_frame func initial actual` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `addressed` >> simp[]) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `addressed` >> simp[]) >>
  qexists_tac `actual` >> asm_rewrite_tac[] >>
  irule abi_decode_sim_trans >> qexists_tac `addressed` >> asm_rewrite_tac[]
QED

Theorem abi_encode_open_none_allocate[local]:
  abi_builtin_encode_setup NONE maxlen st =
    abi_builtin_encode_allocate (32+32*word_size maxlen) 32 st
Proof
  simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_encode_framed_setup_window_open_extend:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_window_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  Cases_on `method_id` >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `mid_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `write_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  rule_assum_tac (SRULE [])
  >- (qpat_x_assum `abi_builtin_encode_setup NONE _ _ = _`
        (assume_tac o REWRITE_RULE [abi_encode_open_none_allocate]) >>
      drule abi_encode_open_allocate_reach >> disch_then drule >>
      disch_then (qspecl_then [`p`, `initial`, `ctx`] mp_tac) >>
      (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size maxlen`] ADD_COMM] >>
        asm_rewrite_tac[])) >> strip_tac >>
      `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
         (32+32*word_size maxlen) p 0 initial actual` by
        gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
          abi_decode_frame_def] >>
      `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size maxlen)` by
        (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
      `abi_encoder_window_input ei at av sb cap actual.vs_memory` by
        (irule abi_encode_setup_frame_window_input >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qexists_tac `actual` >>
      pure_rewrite_tac[Q.SPECL [`32*word_size maxlen`, `32`] ADD_COMM] >> simp[]) >>
  drule abi_encode_open_method_setup_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size (maxlen+4)`] ADD_COMM] >>
    asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_window_input ei at av sb cap actual.vs_memory` by
    (irule abi_encode_setup_frame_window_input >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `actual` >>
  pure_rewrite_tac[Q.SPECL [`32*word_size (maxlen+4)`, `32`] ADD_COMM] >> simp[]
QED

Theorem abi_encode_framed_setup_window_open:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_window_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_framed_setup_window_open_extend >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_encode_window_setup_observed_open:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_window_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_framed_setup_window_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> simp[]
QED
