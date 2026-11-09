(* The tracked staging copy preserves the logical statement state. *)
Theory widenedStagingState
Ancestors
  widenedMemoryStaging exprSimCopy exprSimAlloc exprSimStorageCopy
  abiBuiltinAllocation emitHelperProps loweringHalt abiTupleProps
  freshWrites compileEnv context venomState venomInst list rich_list
  abiDecoderFrame fragExec exprLoweringProps

Theorem compile_staging_prefix_state_mem:
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
       (!x. op = Var x ==> not_fresh_at sa x) ==> eval_operand op t = SOME w) /\
    stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >> drule_all compile_staging_prefix_forward_mem >>
  disch_then (qx_choose_then `r` (qx_choose_then `t` (qx_choose_then `tw`
    (map_every assume_tac o CONJUNCTS)))) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `copy_static t = copy_static r /\ LENGTH r.vs_memory <= LENGTH t.vs_memory` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|>) = r` mp_tac >>
     qpat_x_assum `r.vs_memory = s.vs_memory` mp_tac >>
     qpat_x_assum `LENGTH s.vs_memory <= LENGTH t.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[copy_static_def, venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule copy_buffer_state_rel_frame >>
     first_assum (irule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `local_ptrs_reserved _ _`)) >>
     first_assum (irule_at (Pat `MEM _ (fn_insts _)`)) >>
     simp[mk_inst_def] >> conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _` drule_all >>
        simp[regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`r`, `t`, `tw`] >> asm_rewrite_tac[]
QED
