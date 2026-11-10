Theory exprSimAbiEncodeTupleSuccess
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeTupleExecution exprSimAbiEncodeExecFrame
  exprSimHash abiTupleEncodePrepare abiTupleEncodeSlot
  context compileEnv abiTupleProps emitHelper emitHelperProps exprLoweringProps exprLowering
  fragExec venomInst list rich_list arithmetic intCallCallee
  stmtSimLogExecFields exprSimAbiEncodeSemantic exprSimAbiEncodeMemoryLength
  ctorAbiActualAlloc exprSimCopy exprSimStorageCopy abiDecoderReservation venomState
  exprSimAlloc abiDecoderContract

Theorem abi_encode_tuple_slot_opcodes:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MSTORE; MCOPY]) (emitted_insts st final)
Proof
  Cases_on `is_word_type ty` >> Cases_on `type_memory_bytes ce ty` >>
  asm_simp_tac (srw_ss()) [compile_abi_tuple_slot_def, compile_copy_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_tuple_store_opcodes:
  !xs ce buf off st final.
  compile_store_abi_tuple ce buf off xs st = ((),final) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MSTORE; MCOPY]) (emitted_insts st final)
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac [EVERY_APPEND] >> conj_tac
  >- (drule abi_encode_tuple_slot_opcodes >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem abi_encode_tuple_stage_opcodes:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; MSTORE; MCOPY]) (emitted_insts st staged)
Proof
  strip_tac >>
  drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac [EVERY_APPEND] >> conj_tac
  >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      simp[contextTheory.compile_alloc_buffer_def, emit_op_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule abi_encode_tuple_store_opcodes >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_tuple_staging_path:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st staged) s = OK actual ==>
  gas_marked_path F ctx func s 0
    (OK (actual with vs_inst_idx := LENGTH staged.cs_current_insts)) /\
  ~actual.vs_halted /\ actual.vs_current_bb = staged.cs_current_bb
Proof
  strip_tac >> drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  `staged.cs_current_insts = st.cs_current_insts ++ emitted_insts st staged` by
    fs[inst_extends_def] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st staged)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem abi_encode_tuple_staging_external:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  run_inst_seq (emitted_insts st staged) s = OK actual ==>
  log_encode_external actual = log_encode_external s
Proof
  strip_tac >> drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  irule log_encode_run_external >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED

Theorem abi_encode_tuple_staging_exec_frame:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  run_inst_seq (emitted_insts st staged) s = OK actual ==>
  abi_encode_exec_frame func s actual
Proof
  strip_tac >> drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  drule_all abi_encode_tuple_staging_external >>
  disch_then (strip_assume_tac o MATCH_MP log_encode_external_fields) >>
  simp[abi_encode_exec_frame_def, abi_encode_semantic_obs_fields] >> conj_tac
  >- (irule run_inst_seq_static_charge >>
      goal_assum (drule_at Any) >> simp[EVERY_MEM] >> gen_tac >> disch_tac >>
      conj_tac >- (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
      fs[EVERY_MEM] >> first_x_assum drule >> strip_tac >> simp[]) >>
  irule abi_encode_leaf_sequence_memory_length >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_tuple_slot_outputs:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) ==>
  EVERY (\i. EVERY (\x. ~not_fresh_at st x) i.inst_outputs) (emitted_insts st final)
Proof
  Cases_on `is_word_type ty` >> Cases_on `type_memory_bytes ce ty` >>
  asm_simp_tac (srw_ss()) [compile_abi_tuple_slot_def, compile_copy_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def]
QED

Theorem abi_encode_tuple_store_outputs:
  !xs ce buf off st final.
  compile_store_abi_tuple ce buf off xs st = ((),final) ==>
  EVERY (\i. EVERY (\x. ~not_fresh_at st x) i.inst_outputs) (emitted_insts st final)
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac [EVERY_APPEND] >> conj_tac
  >- (drule abi_encode_tuple_slot_outputs >> simp[]) >>
  `EVERY (\i. EVERY (\x. ~not_fresh_at middle x) i.inst_outputs)
     (emitted_insts middle final)` by (first_x_assum irule >> metis_tac[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (emitted_insts middle final) ==> _` drule >>
  disch_then drule >> simp[not_fresh_at_def] >>
  qpat_x_assum `not_fresh_at st x` mp_tac >> simp[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_ADD]
QED

Theorem abi_encode_tuple_store_lookup:
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  run_inst_seq (emitted_insts st final) s = OK actual ==>
  !x. not_fresh_at st x ==> lookup_var x actual = lookup_var x s
Proof
  strip_tac >> drule abi_tuple_encode_store_shape >> strip_tac >>
  drule abi_encode_tuple_store_outputs >> strip_tac >> gen_tac >> strip_tac >>
  irule ctor_actual_sequence_var_frame >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_tuple_store_static:
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  run_inst_seq (emitted_insts st final) s = OK actual ==>
  copy_static actual = copy_static s
Proof
  strip_tac >> drule abi_encode_tuple_store_opcodes >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `log_encode_external actual = log_encode_external s` by
    (irule log_encode_run_external >> goal_assum (drule_at Any) >>
     fs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]) >>
  `actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >> goal_assum (drule_at Any) >>
     fs[EVERY_MEM] >> gen_tac >> strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts st final) ==> _ \/ _ \/ _` drule >>
     strip_tac >> simp[is_alloca_op_def]) >>
  fs[log_encode_external_def, copy_static_def, venom_state_component_equality]
QED

Theorem abi_encode_tuple_staging_split:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  n < dimword (:256) /\
  run_inst_seq (emitted_insts st staged) s = OK actual /\
  FLOOKUP actual.vs_allocas st.cs_next_id = SOME (b,n) ==>
  ?addressed.
    stmt_state_rel ctx func ce cx es addressed /\
    run_inst_seq (emitted_insts allocated staged) addressed = OK actual /\
    addressed.vs_memory = s.vs_memory /\ copy_static actual = copy_static addressed /\
    FLOOKUP addressed.vs_allocas st.cs_next_id = SOME (b,n) /\
    b + n < dimword (:256) /\
    (!x. not_fresh_at st x ==> lookup_var x addressed = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP addressed.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint b n a len) /\
    (!name a len. local_region ce es.scopes addressed name a len ==>
       regions_disjoint b n a len)
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >>
  disch_then (qx_choose_then `addressed` (qx_choose_then `w` strip_assume_tac)) >>
  drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq (emitted_insts allocated staged) addressed = OK actual` by
    (qpat_x_assum `run_inst_seq (emitted_insts st staged) s = _` mp_tac >>
     drule run_inst_seq_append >> disch_then (qspec_then `emitted_insts allocated staged` mp_tac) >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  drule_all abi_encode_tuple_store_static >> strip_tac >>
  `actual.vs_allocas = addressed.vs_allocas` by metis_tac[copy_static_fields] >>
  `b = w2n w` by gvs[] >> gvs[] >> qexists `addressed` >> simp[] >> metis_tac[]
QED

Theorem abi_encode_tuple_staging_state_rel:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  n < dimword (:256) /\
  run_inst_seq (emitted_insts st staged) s = OK actual /\
  abi_decode_frame b n s actual /\
  FLOOKUP actual.vs_allocas st.cs_next_id = SOME (b,n) ==>
  stmt_state_rel ctx func ce cx es actual
Proof
  strip_tac >>
  drule_all abi_encode_tuple_staging_split >>
  disch_then (qx_choose_then `addressed` strip_assume_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  irule copy_buffer_state_rel_frame >>
  qexistsl [`b`, `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]`, `addressed`, `allocated`, `n`] >>
  asm_rewrite_tac [mk_inst_def] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def])
  >- metis_tac[abi_encode_tuple_store_lookup]
  >- (fs[abi_decode_frame_def] >> metis_tac[])
  >- (qpat_x_assum `addressed.vs_memory = s.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
      irule abi_encode_leaf_sequence_memory_length >>
      qexists `emitted_insts allocated staged` >> asm_rewrite_tac [] >>
      drule abi_encode_tuple_store_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
  simp[] >> irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >>
  drule abi_tuple_encode_alloc_shape >> simp[]
QED

Theorem abi_encode_tuple_staging_origin_frame:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es' s /\ local_ptrs_reserved ce st /\
  n < dimword (:256) /\
  run_inst_seq (emitted_insts st staged) s = OK actual /\
  abi_decode_frame b n s actual /\
  FLOOKUP actual.vs_allocas st.cs_next_id = SOME (b,n) /\
  wb_frame ce es es' origin s0 s /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  wb_frame ce es es' origin s0 actual
Proof
  strip_tac >> drule_all abi_encode_tuple_staging_split >>
  disch_then (qx_choose_then `addressed` strip_assume_tac) >>
  drule abi_tuple_encode_alloc_shape >> strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at allocated x` by fs[not_fresh_at_def] >>
     drule_all abi_encode_tuple_store_lookup >> simp[]) >>
  `actual.vs_allocas = addressed.vs_allocas` by metis_tac[copy_static_fields] >>
  irule wb_frame_allocating_tail >> asm_rewrite_tac [] >>
  qexistsl [`s`, `es'.scopes`, `st`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      `local_region ce es'.scopes addressed n' b' sz` by
        (qpat_x_assum `!x. not_fresh_at st x ==> lookup_var x actual = _` kall_tac >>
         drule_all copy_buffer_local_region_frame >> simp[]) >>
      fs[abi_decode_frame_def] >>
      qpat_x_assum `!name a len. _ ==> regions_disjoint _ _ _ _` drule >>
      simp[regions_disjoint_def] >> strip_tac >>
      qpat_x_assum `!p k. _ ==> mem_bytes_at _ _ actual.vs_memory = _` irule >>
      simp[ADD_COMM])
  >- (rpt strip_tac >> fs[abi_decode_frame_def] >>
      qpat_x_assum `!aid a len. _ ==> regions_disjoint _ _ _ _` drule >>
      simp[regions_disjoint_def] >> strip_tac >>
      qpat_x_assum `!p k. _ ==> mem_bytes_at _ _ actual.vs_memory = _` irule >>
      simp[ADD_COMM])
QED

Theorem abi_encode_tuple_wb_frame_cursor[local]:
  wb_frame ce es es' origin s0 (s with vs_inst_idx := k) <=>
  wb_frame ce es es' origin s0 s
Proof
  simp[loweringPostsTheory.wb_frame_def, exprSimPropsTheory.locals_kept_inst_idx,
       lookup_var_def]
QED

Theorem abi_encode_tuple_staging_cursor:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st allocated func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es' s /\ local_ptrs_reserved ce st /\
  n < dimword (:256) /\
  run_inst_seq (emitted_insts st staged) s = OK actual /\
  abi_decode_frame b n s actual /\
  FLOOKUP actual.vs_allocas st.cs_next_id = SOME (b,n) /\
  wb_frame ce es es' origin s0 s /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  stmt_state_rel ctx func ce cx es'
    (actual with vs_inst_idx := LENGTH staged.cs_current_insts) /\
  wb_frame ce es es' origin s0
    (actual with vs_inst_idx := LENGTH staged.cs_current_insts)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx, abi_encode_tuple_wb_frame_cursor] >>
  conj_tac >- (irule abi_encode_tuple_staging_state_rel >> metis_tac[]) >>
  irule abi_encode_tuple_staging_origin_frame >> metis_tac[]
QED
