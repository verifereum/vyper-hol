(* Finite memory-safe full-layout copy prefixes for widened values. *)
Theory widenedMemoryStaging
Ancestors
  bodyCopyMemory exprSimMemUnwrap placeMemoryStaging
  placeMemoryTypedPrimitive fragGasMode list rich_list loweringHalt
  abiTupleProps fragExec compileEnv exprLoweringProps exprSimBufferStore
  exprSimProps venomState valueEncodingProps venomExecSemantics
  abiBuiltinAllocation emitHelperProps venomInst finite_map words arithmetic
  instIdxIndep fragGasPathMem placeMemoryCopyFrames

Theorem compile_copy_memory_path_mem_endpoint[local]:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func
    ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_copy_memory_body_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all straight_path_mem >> simp[]
QED

Theorem compile_staging_prefix_path_mem[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ alloca_history func s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ w2n sw + n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r tw. gas_path_mem ctx func s 0 (OK r) /\
    stmt_state_rel ctx func ce cx es r /\
    eval_operand src r = SOME sw /\ eval_operand buf.buf_operand r = SOME tw /\
    r.vs_memory = s.vs_memory /\ alloca_history func r /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP r.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n tw) n b len) /\
    (!name b len. local_region ce es.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    s.vs_alloca_next <= r.vs_alloca_next /\
    contract_storage r = contract_storage s /\
    contract_transient r = contract_transient s /\ r.vs_labels = s.vs_labels /\
    (?q. run_inst_seq (emitted_insts sa sm) s = OK q /\
         r = q with vs_inst_idx := LENGTH sm.cs_current_insts) /\
    w2n sw + n <= r.vs_alloca_next /\
    w2n tw + n <= r.vs_alloca_next /\ w2n tw + n < dimword (:256) /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    gas_path_mem ctx func r 0
      (OK ((if n = 0 then r else mcopy (w2n tw) (w2n sw) n r)
        with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
    alloca_history func
      ((if n = 0 then r else mcopy (w2n tw) (w2n sw) n r)
        with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `w2n sw + n <= u.vs_alloca_next` by decide_tac >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  drule_all compile_copy_memory_path_mem_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

Theorem compile_copy_memory_value_path_mem[local]:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    (t with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!a k. a + k <= w2n dw \/ w2n dw + n <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  drule_all buffer_copy_memory_encoding >> strip_tac >>
  `q = if n = 0 then s else mcopy (w2n dw) (w2n sw) n s` by gvs[] >>
  drule_all compile_copy_memory_path_mem_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(q with vs_memory := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    (Cases_on `n = 0` >> simp[mcopy_memory_length]) >>
  qpat_assum `(q with vs_memory := _) = s`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[] >> gvs[venom_state_component_equality, same_blocks_def] >> metis_tac[]
QED

Theorem alloc_buffer_run_effect[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK q /\
  eval_operand buf.buf_operand q = SOME w /\
  FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
  n < dimword (:256) /\ s.vs_alloca_next < dimword (:256) ==>
  ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n w = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,n)) /\
  (q with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next|>) = s
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >>
  asm_rewrite_tac[run_inst_seq_def, step_inst_base_def, mk_inst_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (simp[exec_alloca_def] >> strip_tac >>
      gvs[update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
          wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
      simp[venom_state_component_equality]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME entry` >>
  PairCases_on `entry` >> simp[exec_alloca_def] >> strip_tac >>
  gvs[update_var_def, lookup_var_def, eval_operand_def, venom_state_component_equality]
QED

Theorem compile_staging_prefix_forward_mem:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n = type_memory_size tv /\
  val_wf tv v /\ val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + n <= s.vs_alloca_next ==>
  ?r t tw. gas_path_mem ctx func s 0 (OK r) /\
    stmt_state_rel ctx func ce cx es r /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw + n < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= r.vs_alloca_next /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP r.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n tw = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n tw,n)) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
       vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    gas_path_mem ctx func r 0 (OK t) /\ gas_path_mem ctx func s 0 (OK t) /\
    val_in_memory tv v (w2n tw) t.vs_memory /\
    t.vs_allocas = r.vs_allocas /\
    (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
       vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
       vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a len. a + len <= w2n tw \/ w2n tw + n <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!name b len. local_region ce es.scopes r name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME tw /\
    alloca_history func r /\ alloca_history func t /\
    w2n tw + n <= t.vs_alloca_next /\
    (!op w. eval_operand op s = SOME w /\
       (!x. op = Var x ==> not_fresh_at sa x) ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all compile_staging_prefix_path_mem >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `eval_operand buf.buf_operand q = SOME tw /\
   FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n tw,n)` by
    gvs[eval_op_inst_idx] >>
  drule_all alloc_buffer_run_effect >> strip_tac >>

  `cs_extends sa sm /\ cs_extends sm sn` by
    (conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `alloca_inv r /\ val_in_memory tv v (w2n sw) r.vs_memory /\
   val_footprint tv v <= n` by fs[stmt_state_rel_def, val_footprint_le] >>
  drule_all compile_copy_memory_value_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (drule_all gas_path_mem_then >> simp[]) >>

  `t.vs_vars = r.vs_vars /\ t.vs_labels = s.vs_labels` by
    gvs[venom_state_component_equality] >>
  `!op w. eval_operand op s = SOME w /\
     (!x. op = Var x ==> not_fresh_at sa x) ==> eval_operand op t = SOME w` by
    (rpt gen_tac >> strip_tac >> Cases_on `op` >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `!name b len. local_region ce es.scopes r name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!nm base size. local_region _ _ _ nm base size ==> _` drule_all >>
     simp[regions_disjoint_def] >> strip_tac >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k _ = _`
       (qspecl_then [`b`, `len`] mp_tac) >> simp[]) >>
  qexistsl_tac [`r`, `t`, `tw`] >> gvs[] >>
  gvs[venom_state_component_equality, regions_disjoint_def,
      eval_operand_def, lookup_var_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED
