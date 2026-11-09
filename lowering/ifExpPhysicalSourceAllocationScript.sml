Theory ifExpPhysicalSourceAllocation
Ancestors
  exprSimMemUnwrap exprSimIfExp exprSimTypedAlloc
  context compileEnv venomExecSemantics venomInst emitHelper fragExec
Libs
  intLib

(* Ownership, not frontier growth, separates the physical source from the
   allocation.  Sources may live either in an earlier alloca or a local. *)
Theorem ifexp_allocate_physical_source:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sz < dimword (:256) /\
  expr_val_at ce cx sty origin sa es v src s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  0 < type_memory_size stv /\
  eval_operand src s = SOME sw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_path_mem ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand src u = SOME sw /\ eval_operand buf.buf_operand u = SOME w /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n w + sz < dimword (:256) /\ w2n w + sz <= u.vs_alloca_next /\
    regions_disjoint (w2n w) sz (w2n sw) (type_memory_size stv) /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    u.vs_memory = s.vs_memory /\ sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\ u.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all expr_val_at_bound >>
     `val_footprint stv v = type_memory_size stv` by
       metis_tac[ifexp_aggregate_footprint] >>
     simp[]) >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >>
  `regions_disjoint (w2n w) sz (w2n sw) (type_memory_size stv)` by
    (drule_all ifexp_aggregate_source_region >> strip_tac >> gvs[]
     >- (qpat_x_assum `!aid b len. _` drule >> simp[] >>
         gvs[regions_disjoint_def] >> decide_tac) >>
     `local_region ce es.scopes u n b sz'` by
       (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >>
        metis_tac[]) >>
     qpat_x_assum `!name b len. _` drule >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
