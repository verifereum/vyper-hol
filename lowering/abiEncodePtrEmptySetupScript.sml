Theory abiEncodePtrEmptySetup
Ancestors abiEncodePtrEmptySetupAllocate abiEncodePtrEmptySetupMethod
  abiEncodePtrEmptySetupConcrete abiBuiltinEncodeAllocate abiBuiltinEncodeMethod
  abiBuiltinAllocation abiBuiltinEncodeSetup abiDecoderReentry
  bodyPtrDefs bodyPtrHashBuiltinsAllocFrame assignBasePtrAllocSeparate
  exprSimProps sourceMemoryFrames allocationGrowth
  exprSimAbiEncodeStateTransport localPtrsProps fragGasSeqPtr fragExec
  compileEnv emitHelper emitHelperProps exprLoweringProps
  loweringStateRelDefs venomState venomInst finite_map words list rich_list
  arithmetic pred_set appendStorageStageTransportPtr bodyPtrBopHashFrame

Theorem abi_encode_empty_setup_ptr:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\ fn_inst_ids_distinct func /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+m) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decoder_operand_live st.cs_next_var src /\
  eval_operand src initial = SOME sv /\ op_taint tn src = {} /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  stmt_state_rel ctx func cenv cx es initial /\
  ghost_inv rb cenv cx es G tn initial ==>
  ?raw prepared Gp tnp x.
    run_inst_seq (emitted_insts st ready) initial = OK raw /\
    prepared = raw with vs_inst_idx := LENGTH ready.cs_current_insts /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn initial 0 Gp tnp (OK prepared) /\
    ghost_inv rb cenv cx es Gp tnp prepared /\
    ghost_kept cenv es st G tn initial Gp tnp /\
    FST ops = Var x /\ ptr_covers Gp tnp x prepared outsz /\
    eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w (p+32+m)) /\
    eval_operand src prepared = SOME sv /\
    op_taint tnp (FST ops) = {} /\ op_taint tnp (SND ops) = {} /\
    op_taint tnp src = {} /\
    (method_id <> NONE ==> !i. p+32 <= i /\ i < p+64 ==> i NOTIN tnp.t_mem) /\
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
    abi_encoder_extend_sim ctx func initial prepared /\
    stmt_state_rel ctx func cenv cx es prepared /\
    (!name b k. local_region cenv es.scopes prepared name b k ==>
      regions_disjoint p outsz b k)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_empty_setup_concrete >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule abi_builtin_encode_setup_allocate_trace >> strip_tac >>
  `abi_builtin_encode_allocate outsz (32+m) st = (ops,address_st)` by gvs[] >>
  drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)]
      [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    suspend "membership" >>
  `!v. src = Var v ==> not_fresh_at st v` by
    (Cases_on `src` >> gvs[abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all abi_encode_empty_allocate_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "method_inputs"
QED

Resume abi_encode_empty_setup_ptr[membership]:
  `isPREFIX address_st.cs_current_insts ready.cs_current_insts` by
    (Cases_on `method_id`
     >- gvs[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def, comp_return_def] >>
     drule abi_builtin_encode_method_shape >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)]
      [STRING #"%" (toString st.cs_next_var)]) address_st.cs_current_insts` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_tac o MATCH_MP inst_extends_emit_op) >>
     simp[inst_extends_def] >> strip_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
  qexistsl [`st`, `ready`] >> reverse conj_tac >- asm_rewrite_tac[] >>
  metis_tac[IS_PREFIX_APPEND, MEM_APPEND]
QED

Resume abi_encode_empty_setup_ptr[method_inputs]:
  `cs_extends st address_st /\ cs_extends address_st ready` by
    (conj_tac
     >- simp[abiEncoderChildContextTheory.abi_encoder_straight_extends] >>
     Cases_on `method_id`
     >- gvs[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
          comp_return_def, cs_extends_refl] >>
     drule abi_builtin_encode_method_shape >> strip_tac >>
     irule abiEncoderChildContextTheory.abi_encoder_straight_extends >> simp[]) >>
  `fn_has_code st address_st func /\ fn_has_code address_st ready func` by
    metis_tac[fn_has_code_split] >>
  drule_all exprSimAbiEncodeConcreteBuiltinWrappersTheory.abi_encode_allocate_concrete >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `raw'' = raw'` by
    (qpat_assum `run_inst_seq _ _ = OK raw''` mp_tac >>
     qpat_assum `run_inst_seq _ _ = OK raw'` (fn th => rewrite_tac[th]) >> simp[]) >>
  `actual = addressed` by
    (qpat_assum `actual = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `addressed = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `actual = addressed` SUBST_ALL_TAC >>
  `lookup_var x addressed = SOME (n2w p)` by
    (qpat_assum `eval_operand (FST ops) addressed = SOME (n2w p)` mp_tac >>
     qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
     simp[eval_operand_def]) >>
  `not_fresh_at address_st x` by
    (gvs[not_fresh_at_def] >> qexists `st.cs_next_var` >> simp[]) >>
  `local_ptrs_reserved cenv address_st` by
    (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[]) >>
  `!v k. cenv.ce_return_buf = SOME (PtrVar (Var v) k) ==> not_fresh_at address_st v` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
  `!v k. cenv.ce_return_pc = SOME (PtrVar (Var v) k) ==> not_fresh_at address_st v` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
  suspend "local_inputs"
QED

Resume abi_encode_empty_setup_ptr[local_inputs]:
  `addressed.vs_memory = initial.vs_memory /\ allocation_growth initial addressed` by
    (qpat_assum `abi_builtin_allocation_frame _ _ _ initial addressed` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_builtin_allocation_frame_def] >> strip_tac >>
     simp[allocation_growth_def] >>
     Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` >>
     simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[] >>
     Cases_on `st.cs_next_id = id` >> gvs[]) >>
  `local_ptrs_rel func cenv es.scopes initial` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func cenv es.scopes addressed` by
    (irule local_ptrs_rel_memory_frame >> qexists `initial` >> simp[] >>
     rpt strip_tac >>
     `not_fresh_at st p'` by
       (fs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
     metis_tac[]) >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `emitted_insts st address_st = emitted_insts st allocated ++ emitted_insts allocated address_st` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> irule emitted_insts_append >> asm_rewrite_tac[]) >>
  `run_inst_seq (emitted_insts allocated address_st) t = OK raw'` by
    (qpat_assum `run_inst_seq (emitted_insts st address_st) initial = OK raw'` mp_tac >>
     qpat_assum `emitted_insts st address_st = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts st allocated) initial = OK t`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts allocated address_st` (fn th => rewrite_tac[th])) >> simp[]) >>
  `lookup_var p' raw' = lookup_var p' t` by
    (irule emit_op_old_lookup >>
     qexistsl [`ADD`, `[buf.buf_operand; Lit (n2w (32+m))]`, `data_ptr`, `allocated`, `address_st`] >>
     simp[is_terminator_def]) >>
  `w' = n2w p` by
    (qpat_assum `eval_operand buf.buf_operand t = SOME w'` mp_tac >>
     qpat_assum `buf.buf_operand = Var p'` (fn th => rewrite_tac[th]) >>
     simp[eval_operand_def] >>
     qpat_assum `lookup_var x addressed = SOME (n2w p)` mp_tac >>
     `x = p'` by
       (qpat_assum `FST ops = Var x` mp_tac >>
        qpat_assum `ops = (buf.buf_operand,data_ptr)` (fn th => rewrite_tac[th]) >>
        qpat_assum `buf.buf_operand = Var p'` (fn th => rewrite_tac[th]) >> simp[]) >>
     qpat_assum `addressed = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `lookup_var p' raw' = lookup_var p' t` mp_tac >>
     qpat_assum `x = p'` (fn th => rewrite_tac[th]) >>
     qpat_assum `raw'' = raw'` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[lookup_var_def] >> metis_tac[]) >>
  suspend "separation"
QED

Resume abi_encode_empty_setup_ptr[separation]:
  `!name b k. local_region cenv es.scopes addressed name b k <=>
              local_region cenv es.scopes t name b k` by
    (rpt gen_tac >>
     irule bodyPtrBopHashFrameTheory.bop_local_region_readonly_frame >>
     qexists `st` >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  `!name b k. local_region cenv es.scopes addressed name b k ==> regions_disjoint p outsz b k` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name b k` by metis_tac[] >>
     qpat_assum `!name b k. local_region cenv es.scopes t name b k ==> _` drule >>
     simp[wordsTheory.w2n_n2w]) >>
  `method_id <> NONE ==> 64 <= outsz` by
    (Cases_on `method_id` >> simp[] >>
     `m = 4` by simp[] >>
     `word_size (maxlen + m) <> 0` by
       simp[eventTopicValuePropsTheory.word_size_zero] >>
     qpat_assum `outsz = 32 + _` (fn th => rewrite_tac[th]) >>
     qpat_assum `word_size (maxlen + m) <> 0` mp_tac >>
     qpat_assum `m = 4` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!name b k. method_id <> NONE /\ local_region cenv es.scopes addressed name b k ==>
      regions_disjoint (p+32) 32 b k` by
    (rpt strip_tac >>
     `regions_disjoint p outsz b k` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `abi_builtin_encode_method_id method_id (Var x) address_st = ((),ready)` by metis_tac[] >>
  `st.cs_next_var <= address_st.cs_next_var` by simp[] >>
  `method_id <> NONE ==> 64 <= outsz /\ p+32 < dimword (:256)` by simp[] >>
  drule_all abi_encode_empty_method_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "compose"
QED

Resume abi_encode_empty_setup_ptr[compose]:
  `inst_extends address_st ready` by
    (Cases_on `method_id`
     >- gvs[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
          comp_return_def, inst_extends_refl] >>
     drule abi_builtin_encode_method_shape >> strip_tac >> simp[inst_extends_def]) >>
  `emitted_insts st ready = emitted_insts st address_st ++ emitted_insts address_st ready` by
    (irule emitted_insts_append >> metis_tac[inst_extends_def]) >>
  `LENGTH address_st.cs_current_insts = initial.vs_inst_idx + LENGTH (emitted_insts st address_st)` by
    (qpat_assum `initial.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `inst_extends st address_st`
       (mp_tac o Q.AP_TERM `LENGTH` o REWRITE_RULE [inst_extends_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `inst_seq_ptr (cx_dead cx) 0 ctx func PG G tn (emitted_insts st ready) initial H tm` by
    (qpat_assum `emitted_insts st ready = _` (fn th => rewrite_tac[th]) >>
     irule bodyPtrBopScalarSeqTheory.bop_inst_seq_ptr_append >>
     metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts address_st ready)` by
    (qpat_assum `EVERY _ (emitted_insts st ready)` mp_tac >>
     qpat_assum `emitted_insts st ready = _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts address_st ready) raw' = OK raw` by
    (qpat_assum `run_inst_seq (emitted_insts st ready) initial = OK raw` mp_tac >>
     qpat_assum `emitted_insts st ready = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts st address_st) initial = OK raw'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[exprLoweringPropsTheory.run_inst_seq_append]) >>
  `run_inst_seq (emitted_insts address_st ready) addressed =
      OK (raw with vs_inst_idx := LENGTH address_st.cs_current_insts)` by
    (qpat_assum `addressed = raw' with vs_inst_idx := _` (fn th => rewrite_tac[th]) >>
     simp[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]) >>
  `t' = prepared` by
    (qpat_assum `t' = _ with vs_inst_idx := _` mp_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts address_st ready) addressed = OK (raw with vs_inst_idx := _)` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts address_st ready) addressed = OK _` mp_tac >>
     qpat_assum `prepared = raw with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `ghost_inv rb cenv cx es H tm prepared /\ ptr_covers H tm x prepared outsz` by
    (qpat_assum `ghost_inv rb cenv cx es H tm t'` mp_tac >>
     qpat_assum `ptr_covers H tm x t' outsz` mp_tac >>
     qpat_assum `t' = prepared` (fn th => rewrite_tac[th]) >> simp[]) >>
  qexistsl [`raw`, `prepared`, `H`, `tm`, `x`] >>
  simp[] >>
  suspend "post"
QED

Resume abi_encode_empty_setup_ptr[post]:
  conj_tac >- suspend "gas" >>
  `op_taint tna (Var x) = {}` by metis_tac[] >>
  `!v. src = Var v ==> not_fresh_at address_st v` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!v. data_ptr = Var v ==> not_fresh_at address_st v` by
    (qpat_assum `emit_op ADD _ _ = (data_ptr,address_st)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     strip_tac >> drule loweringShapeRulesTheory.emit_op_facts >>
     strip_tac >> gvs[]) >>
  `op_taint tm data_ptr = {} /\ op_taint tm src = {}` by
    (qpat_assum `!v. not_fresh_at address_st v ==> _` mp_tac >>
     qpat_assum `!v. data_ptr = Var v ==> _` mp_tac >>
     qpat_assum `!v. src = Var v ==> not_fresh_at address_st v` mp_tac >>
     qpat_assum `op_taint tna (SND ops) = {}` mp_tac >>
     qpat_assum `op_taint tna src = {}` mp_tac >>
     qpat_assum `ops = (_,data_ptr)` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >>
     Cases_on `data_ptr` >> Cases_on `src` >>
     gvs[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  simp[] >>
  conj_tac >- (Cases_on `method_id` >> simp[]) >>
  suspend "caller"
QED

Resume abi_encode_empty_setup_ptr[gas]:
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st ready) = []` by
    (qpat_assum `abi_builtin_encode_setup _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `method_id` >>
     simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_def,
       abiBuiltinEncodeAllocateTheory.abi_builtin_encode_allocate_def,
       abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  `ready.cs_current_bb = st.cs_current_bb` by
    metis_tac[abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape] >>
  `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st ready) (DROP initial.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code st ready func` mp_tac >>
     qpat_assum `inst_extends st ready` mp_tac >>
     qpat_assum `ready.cs_current_bb = st.cs_current_bb` mp_tac >>
     qpat_assum `initial.vs_current_bb = st.cs_current_bb` mp_tac >>
     qpat_assum `initial.vs_inst_idx = LENGTH st.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fn_has_code_def, inst_extends_def] >> rpt strip_tac >> gvs[] >>
     fs[IS_PREFIX_APPEND] >> gvs[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `initial.vs_inst_idx + LENGTH (emitted_insts st ready) = LENGTH ready.cs_current_insts` by
    (qpat_assum `inst_extends st ready` mp_tac >>
     qpat_assum `initial.vs_inst_idx = LENGTH st.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Resume abi_encode_empty_setup_ptr[caller]:
  `?V. addressed = (t with vs_vars := V) with vs_inst_idx := LENGTH address_st.cs_current_insts` by
    (qpat_assum `emit_op ADD _ allocated = (data_ptr,address_st)` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts allocated address_st) t = OK raw'` mp_tac >>
     qpat_assum `addressed = raw' with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq _ t = OK raw'` mp_tac >>
     simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       mk_inst_def, venomExecSemanticsTheory.exec_pure2_def] >>
     Cases_on `eval_operand buf.buf_operand t` >>
     simp[eval_operand_def] >> strip_tac >>
     gvs[update_var_def] >> metis_tac[]) >>
  `!v. not_fresh_at st v ==> lookup_var v addressed = lookup_var v t` by
    (qpat_assum `!v. not_fresh_at st v ==> lookup_var v addressed = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es addressed` by
    (qpat_assum `addressed = (t with vs_vars := _) with vs_inst_idx := _`
       (fn th => rewrite_tac[th]) >>
     rewrite_tac[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_vars_frame >> simp[] >>
     qpat_assum `addressed = (t with vs_vars := _) with vs_inst_idx := _` mp_tac >>
     qpat_assum `!v. not_fresh_at st v ==> lookup_var v addressed = lookup_var v t` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv st` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[local_ptrs_reserved_def, lookup_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes addressed name b k` by
        (irule local_region_frame >>
         metis_tac[]) >>
      `regions_disjoint p outsz b k` by metis_tac[] >>
      qpat_assum `outsz = _` mp_tac >>
      qpat_assum `m = _` mp_tac >>
      qpat_assum `regions_disjoint p outsz b k` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  suspend "method_caller"
QED

Resume abi_encode_empty_setup_ptr[method_caller]:
  Cases_on `method_id`
  >- (qpat_assum `abi_builtin_encode_method_id NONE _ _ = _` mp_tac >>
      qpat_assum `run_inst_seq (emitted_insts address_st ready) addressed = OK (raw with vs_inst_idx := _)` mp_tac >>
      qpat_assum `stmt_state_rel ctx func cenv cx es addressed` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
        comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_def, stmt_state_rel_inst_idx]) >>
  rename1 `abi_builtin_encode_method_id (SOME mid) _ _ = _` >>
  `stmt_state_rel ctx func cenv cx es (mstore (p+32) (mid << 224) addressed)` by
    (irule exprSimAllocTheory.literal_mstore_state_rel >>
     (reverse conj_tac >- simp[]) >>
     qexistsl [`p`, `mk_inst st.cs_next_id ALLOCA [Lit (n2w outsz)] [STRING #"%" (toString st.cs_next_var)]`, `outsz`] >>
     simp[mk_inst_def] >>
     qpat_assum `!name b k. local_region cenv es.scopes addressed name b k ==> regions_disjoint p outsz b k` mp_tac >>
     qpat_assum `!name b k. local_region cenv es.scopes addressed name b k <=> _` mp_tac >>
     qpat_assum `SOME mid <> NONE ==> 64 <= outsz` mp_tac >>
     qpat_assum `outsz = _` mp_tac >> qpat_assum `m = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `?V. prepared = (mstore (p+32) (mid << 224) addressed with vs_vars := V)
      with vs_inst_idx := LENGTH ready.cs_current_insts` by
    (`?dst. emitted_insts address_st ready =
       [mk_inst address_st.cs_next_id ADD [Var x; Lit 32w] [dst];
        mk_inst (address_st.cs_next_id+1) MSTORE [Var dst; Lit (mid << 224)] []]` by
       (qpat_assum `abi_builtin_encode_method_id (SOME mid) (Var x) address_st = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
        strip_tac >> gvs[emitted_insts_def, DROP_APPEND1] >>
        qexists `STRING #"%" (toString address_st.cs_next_var)` >> simp[]) >>
     qpat_assum `run_inst_seq (emitted_insts address_st ready) addressed = OK (raw with vs_inst_idx := _)` mp_tac >>
     qpat_assum `emitted_insts address_st ready = [_;_]` mp_tac >>
     qpat_assum `lookup_var x addressed = SOME (n2w p)` mp_tac >>
     qpat_assum `SOME mid <> NONE ==> p+32 < dimword (:256)` mp_tac >>
     qpat_assum `prepared = raw with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       mk_inst_def, venomExecSemanticsTheory.exec_pure2_def, eval_operand_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venomExecSemanticsTheory.exec_write2_def, word_add_n2w] >>
     qexists `addressed.vs_vars |+ (dst,n2w (p+32))` >>
     qpat_x_assum `mstore _ _ _ = _`
       (mp_tac o Q.AP_TERM `\s. s with vs_inst_idx := LENGTH ready.cs_current_insts`) >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  `stmt_state_rel ctx func cenv cx es prepared` suffices_by metis_tac[stmt_state_rel_inst_idx] >>
  qpat_x_assum `prepared = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `addressed = (t with vs_vars := _) with vs_inst_idx := _` kall_tac >>
  qpat_assum `prepared = (mstore _ _ _ with vs_vars := _) with vs_inst_idx := _`
    (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_vars_frame >> simp[] >>
  qpat_assum `prepared = (mstore _ _ _ with vs_vars := _) with vs_inst_idx := _` mp_tac >>
  qpat_assum `!v. not_fresh_at address_st v ==> lookup_var v t' = _ /\ _` mp_tac >>
  qpat_assum `t' = prepared` mp_tac >>
  qpat_assum `local_ptrs_reserved cenv address_st` mp_tac >>
  qpat_assum `addressed = raw' with vs_inst_idx := _` mp_tac >>
  qpat_assum `addressed = raw'' with vs_inst_idx := _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[local_ptrs_reserved_def, lookup_var_def, mstore_def,
    write_memory_with_expansion_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Finalise abi_encode_empty_setup_ptr
