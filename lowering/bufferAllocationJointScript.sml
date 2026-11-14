(* Joint buffer allocation and ownership, moved without statement changes. *)
Theory bufferAllocationJoint
Ancestors
  bodyPtrEnvBuiltinsAllocation bodyFullUnwrapRun bodyFullGhostFrame
  emitHelper fragGasSeqPtr fragExecPtr fragExecMem venomMemDefs bodyPtrDefs
  exprSimAlloc exprLoweringProps allocationPtr ptrSafetyTransport
  compileEnv context emitHelperProps venomState venomInst venomExecSemantics
  ptrDiscipline codegenRel contextCodegenRel loweringStateRelDefs fragExec fragGasOriginPtr
  list finite_map

Theorem return_default_alloc_joint:
  compile_alloc_buffer n a = (buf,b) /\ fn_has_code a b func /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (r with vs_inst_idx := LENGTH b.cs_current_insts),
     step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]) r,
     step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]) s r tn)
Proof
  strip_tac >> gen_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]] /\
   emitted_insts a b = [mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString a.cs_next_var)]]` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def, emitted_insts_def] >> simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts a b`, `a`] >> simp[is_terminator_def] >>
  conj_tac >- suspend "mem" >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  simp[inst_seq_ptr_def] >>
  irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >> simp[] >>
  qexists_tac `0` >> simp[ptr_inst_ok_alloca]
QED
Resume return_default_alloc_joint[mem]:
  simp[run_inst_seq_mem_ok_def,
    unitTransformDefsTheory.inst_mem_below_frontier_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  CASE_TAC >> simp[]
QED
Finalise return_default_alloc_joint

Theorem return_default_alloc_ghost_inv_at:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ghost_inv_at D lo d cenv cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >> drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- suspend "return" >>
  conj_tac >- (rpt strip_tac >> `x <> out` by metis_tac[] >> metis_tac[]) >>
  suspend "fixed"
QED
Resume return_default_alloc_ghost_inv_at[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac >- (drule_all alloca_step_old_ptr_covers >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  irule alloca_step_local_robust >> simp[] >> metis_tac[]
QED
Resume return_default_alloc_ghost_inv_at[return]:
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> fs[return_buf_ptr_def] >>
  `x <> out` by metis_tac[] >>
  `ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) x u x1` by
    (drule_all alloca_step_old_ptr_covers >> simp[]) >>
  metis_tac[]
QED
Resume return_default_alloc_ghost_inv_at[fixed]:
  conj_tac >- suspend "storage" >>
  conj_tac >- (rpt strip_tac >> simp[] >> first_x_assum irule >>
    simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  conj_tac >- (rpt strip_tac >> `x <> out` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >> metis_tac[]) >>
  irule ptrSafetyTransportTheory.step_inst_allocas_from >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ctx`, `0`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`] >>
  simp[step_inst_non_invoke, mk_inst_def]
QED
Resume return_default_alloc_ghost_inv_at[storage]:
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  gvs[stor_taint_ok_at_def, step_taint_def, store_taint_def, imm_taint_def,
    adopt_reset_def, mk_inst_def]
QED
Finalise return_default_alloc_ghost_inv_at

Theorem return_default_alloc_ghost_kept_at:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  ~not_fresh_at sa out /\ lo <= s.vs_alloca_next ==>
  ghost_kept_at lo cenv es sa G tn s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  strip_tac >> drule_all alloca_step_ghost_kept >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >>
  rewrite_tac[ghost_kept_def, ghost_kept_at_def] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid off sz i. FLOOKUP _ aid = SOME (off,sz) /\ _ ==> _` irule >>
    simp[] >> qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!n b sz i. _` irule >>
    simp[] >> metis_tac[]) >>
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> metis_tac[]
QED

Theorem return_default_alloc_run_step:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r ==>
  step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString a.cs_next_var)]) s = OK r /\
  b.cs_current_bb = a.cs_current_bb /\
  buf.buf_operand = Var (STRING #"%" (toString a.cs_next_var)) /\
  a.cs_next_var <= b.cs_next_var
Proof
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
    emit_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
    run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()]
QED

Theorem return_default_alloc_control:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK r /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  r.vs_halted = s.vs_halted /\ r.vs_current_bb = s.vs_current_bb /\
  r.vs_returndata = s.vs_returndata /\
  allocas_from lo r /\ lo <= r.vs_alloca_next
Proof
  strip_tac >>
  `allocas_from lo r /\ lo <= r.vs_alloca_next` by
    (irule ptrSafetyTransportTheory.step_inst_allocas_from >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ctx`, `0`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  simp[] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def]
QED

Theorem return_default_alloc_resources:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv a /\ n < dimword (:256) ==>
  !H. stmt_state_rel H ctx func cenv cx ee s ==>
    stmt_state_rel H ctx func cenv cx ee r /\
    (?w. eval_operand buf.buf_operand r = SOME w /\
      FLOOKUP r.vs_allocas a.cs_next_id = SOME (w2n w,n) /\
      w2n w + n < dimword (:256) /\
      (!aid off sz. aid < a.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
        regions_disjoint (w2n w) n off sz) /\
      (!name off sz. local_region cenv ee.scopes r name off sz ==>
        regions_disjoint (w2n w) n off sz)) /\
    r.vs_memory = s.vs_memory /\
    (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP r.vs_allocas aid = SOME entry)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem return_default_alloc_ghost_resources:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r /\
  fn_has_code a b func /\ local_ptrs_reserved cenv a /\
  n < dimword (:256) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) ==>
  !H D lo d. stmt_state_rel H ctx func cenv cx ee s /\
    ghost_inv_at D lo d cenv cx ee G tn s ==>
    ghost_inv_at D lo d cenv cx ee
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn) r /\
    ptr_covers
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn)
      (STRING #"%" (toString a.cs_next_var)) r n /\
    ghost_kept_at lo cenv ee a G tn s
      (step_prov PG G (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) r)
      (step_taint (mk_inst a.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString a.cs_next_var)]) s r tn)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all return_default_alloc_run_step >> strip_tac >>
  `~not_fresh_at a (STRING #"%" (toString a.cs_next_var))` by
    simp[not_fresh_at_def] >>
  conj_tac >- (irule return_default_alloc_ghost_inv_at >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule_all alloca_step_ptr_covers >> simp[]) >>
  irule return_default_alloc_ghost_kept_at >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[ghost_inv_at_def] >> metis_tac[]
QED
