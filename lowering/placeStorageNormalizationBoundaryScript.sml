Theory placeStorageNormalizationBoundary
Ancestors
  exprSimMemUnwrap abiBuiltinAllocation venomExecSemantics context
  emitHelper fragExec finite_map valueEncoding exprLoweringProps venomState
  venomInst instIdxIndep emitHelperProps

(* Identify the row used by this concrete run, including allocation-site replay. *)
Theorem normalization_allocation_row_origin[local]:
  compile_alloc_buffer sz sm = (buf,mid) /\
  run_inst_seq (emitted_insts sm mid) s = OK q /\
  FLOOKUP q.vs_allocas sm.cs_next_id = SOME (b,sz) ==>
  (FLOOKUP s.vs_allocas sm.cs_next_id = NONE /\ b = s.vs_alloca_next) \/
  FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,sz)
Proof
  strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`
  >- (simp[exec_alloca_def] >> strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME entry` >>
  PairCases_on `entry` >> simp[exec_alloca_def] >> strip_tac >>
  gvs[update_var_def]
QED

(* Replay separation is deliberately conditional; a fresh site uses the
   source capacity bound at the OLD frontier, before this allocation. *)
Theorem storage_normalization_allocation_boundary:
  !ctx func cenv cx es sm mid buf sz s src sw stv v.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME sw /\
    (!x. src = Var x ==> not_fresh_at sm x) /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    (type_memory_size stv = 0 \/
     w2n sw + type_memory_size stv <= s.vs_alloca_next) ==>
    ?u w. gas_path_mem ctx func s 0 (OK u) /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand src u = SOME sw /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ w2n w + sz <= u.vs_alloca_next /\
      u.vs_memory = s.vs_memory /\ sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      s.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
      contract_storage u = contract_storage s /\
      contract_transient u = contract_transient s /\
      u.vs_labels = s.vs_labels /\
      (?q. run_inst_seq (emitted_insts sm mid) s = OK q /\
           u = q with vs_inst_idx := LENGTH mid.cs_current_insts) /\
      val_in_memory stv v (w2n sw) u.vs_memory /\
      ((FLOOKUP s.vs_allocas sm.cs_next_id = NONE /\
        w2n w = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,sz)) /\
      ((!b n. FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,n) ==>
           w2n sw + type_memory_size stv <= b \/ b+n <= w2n sw) ==>
        type_memory_size stv = 0 \/
        w2n sw + type_memory_size stv <= w2n w \/
        w2n w + sz <= w2n sw) /\
      (FLOOKUP s.vs_allocas sm.cs_next_id = NONE /\
       0 < type_memory_size stv ==>
       w2n sw + type_memory_size stv <= w2n w)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `((FLOOKUP s.vs_allocas sm.cs_next_id = NONE /\
     w2n w = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,sz))` by
    (irule normalization_allocation_row_origin >>
     goal_assum (drule_at Any) >>
     gvs[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  rpt conj_tac >> metis_tac[]
QED
