(* Earlier-site windows are disjoint from the materialization destination. *)
Theory bodyIntCallAllocatedForcing
Ancestors
  bodyIntCallMaterializeLanding bodyIntCallForcingCode bodyIntCallStorageLanding
  bodyIntCallLiteralLanding exprSimPrecompiles exprLoweringProps compileEnv
  exprSimStorageCopy context venomState words finite_map intCallFrame
  fragGasMode

Theorem earlier_allocated_window_disjoint:
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas site = SOME (dst,sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!p k. Win p k ==> ?aid b len. aid < site /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) ==>
  !p k. Win p k ==> regions_disjoint p k dst sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
  `aid <> site` by decide_tac >>
  `regions_disjoint b len dst sz` by
    (irule state_allocations_disjoint >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem materialization_alloc_window_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
  sz < dimword (:256) /\ allocas_above lo s /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above lo u /\ u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\
    s.vs_alloca_next <= u.vs_alloca_next /\ fresh_vars_wrt sm u /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!p k. Win p k ==> regions_disjoint p k (w2n w) sz) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all materialization_alloc_landing >> strip_tac >>
  `!p k. Win p k ==> regions_disjoint p k (w2n w) sz` by
    (mp_tac (Q.INST [`u` |-> `u`, `s` |-> `s`,
       `site` |-> `sa.cs_next_id`, `dst` |-> `w2n (w:bytes32)`]
       (SPEC_ALL earlier_allocated_window_disjoint)) >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED
