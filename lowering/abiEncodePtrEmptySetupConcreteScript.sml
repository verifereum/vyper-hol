Theory abiEncodePtrEmptySetupConcrete
Ancestors
  exprSimAbiEncodeConcreteBuiltinWrappers exprSimAbiEncodeFramedBuiltin
  abiEncoderExtendSim abiBuiltinEncodeCorrect abiBuiltinEncodeSetup
  abiBuiltinEncodeAllocate abiBuiltinEncodeCode abiDecoderFrame
  compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomInst words list arithmetic rich_list context
  abiBuiltinAllocation abiDecoderContract

Theorem abi_encode_empty_setup_concrete:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+m) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?raw prepared.
    run_inst_seq (emitted_insts st ready) initial = OK raw /\
    prepared = raw with vs_inst_idx := LENGTH ready.cs_current_insts /\
    inst_extends st ready /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st ready) /\
    eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w (p+32+m)) /\
    FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 prepared.vs_memory = abi_builtin_encode_method_bytes mid) /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~prepared.vs_halted /\ prepared.vs_labels = initial.vs_labels /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    (!op v. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME v ==>
      eval_operand op prepared = SOME v) /\
    abi_decode_sim ctx func initial prepared /\
    abi_encode_exec_frame func initial prepared /\
    abi_encoder_extend_sim ctx func initial prepared
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  `?raw prepared.
    run_inst_seq (emitted_insts st ready) initial = OK raw /\
    prepared = raw with vs_inst_idx := LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w (p+32+m)) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 prepared.vs_memory = abi_builtin_encode_method_bytes mid) /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~prepared.vs_halted /\ prepared.vs_labels = initial.vs_labels /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    abi_decode_sim ctx func initial prepared` by
    (Cases_on `method_id` >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     qpat_x_assum `w = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     rule_assum_tac (SRULE [])
     >- (qpat_x_assum `abi_builtin_encode_setup NONE _ _ = _` mp_tac >>
         simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
         pairarg_tac >> simp[] >> strip_tac >>
         qpat_x_assum `ops' = ops` SUBST_ALL_TAC >>
         qpat_x_assum `cs' = ready` SUBST_ALL_TAC >>
         drule abi_encode_allocate_concrete >> disch_then drule >>
         disch_then (qspecl_then [`p`, `initial`, `ctx`] mp_tac) >>
         (impl_tac >- gvs[]) >> strip_tac >>
         qexists_tac `raw` >>
         gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
           abi_decode_frame_def]) >>
     drule abi_encode_method_setup_concrete >> disch_then drule >>
     disch_then (qspecl_then [`p`, `initial`, `ctx`] mp_tac) >>
     (impl_tac >- gvs[]) >> strip_tac >>
     qexistsl_tac [`raw`, `actual`] >> gvs[]) >>
  `FLOOKUP prepared.vs_allocas st.cs_next_id = SOME (p,outsz)` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_extend_sim ctx func initial prepared` by
    (qpat_x_assum `prepared = _` SUBST_ALL_TAC >>
     irule abi_encoder_run_sequence_extend_sim >>
     conj_tac >- simp[] >> qexists_tac `st` >> simp[]) >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st ready)` by
    (qpat_x_assum `abi_builtin_encode_setup _ _ _ = _` mp_tac >>
     Cases_on `method_id` >>
     simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  `abi_encode_exec_frame func initial prepared` by
    (drule_all abi_encode_setup_sequence_frame >> gvs[]) >>
  qexistsl_tac [`raw`, `prepared`] >> simp[] >>
  gvs[abi_builtin_encode_setup_frame_def]
QED
