(* Caller-general memory staging resources, independent of return-PC shape. *)
Theory bodyIntCallStageGeneralMemory
Ancestors
  bodyIntCallStageGeneralWord bodyIntCallStageEndpointMemory
  bodyIntCallFamCallIntStageAllocation bodyIntCallStageEndpointForceGeometry
  bodyIntCallWindowLanding bodyIntCallHeldFrame exprSimCopy
  bodyIntCallStageGeneralInterface exprLoweringProps freshWrites
  loweringPosts bodyMemoryDefs exprSimProps intCallFrame stmtSimProps
  exprSimVVFrame bodyIntCallFamCallIntAllocationGeometry

Theorem stage_resources_frame:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel ctx func ce cx es u /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above lo u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x u = SOME w) /\
  (!a k. prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
  (!n p k. local_region ce es.scopes u n p k ==>
    local_region ce es.scopes s n p k) ==>
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sb u
Proof
  strip_tac >> fs[stage_resources_def] >> rpt conj_tac >> simp[]
  >- metis_tac[local_ptrs_reserved_next_var]
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[]
  >- (irule ret_pc_ok_frame >> qexistsl [`ce`, `s`, `sa`] >> simp[])
  >- (irule return_buf_frame_frame >> qexistsl [`ce`, `s`, `sa`] >> simp[]) >>
  metis_tac[]
QED

Theorem stage_allocation_cont:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel ctx func ce cx es u /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above lo u /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!n p k. local_region ce es.scopes u n p k <=>
    local_region ce es.scopes s n p k) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s es sb u
Proof
  strip_tac >> simp[stage_cont_def] >> conj_tac
  >- (irule stage_resources_frame >> simp[] >> qexistsl [`s`, `sa`] >> simp[]) >>
  simp[wb_frame_def] >> irule locals_kept_mem >> simp[] >>
  fs[stage_resources_def]
QED

Theorem stage_memory_allocation_landing:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stage_cont ctx func cx lo prot staged reserved morig oorig rb
      ce env es sa s es sb u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\
    sa.cs_next_id < sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!name b len. local_region ce es.scopes u name b len <=>
      local_region ce es.scopes s name b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
   allocas_above lo s` by fs[stage_resources_def] >>
  drule_all (SRULE [] (Q.INST
    [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sa x`, `sm` |-> `sb`]
    materialization_alloc_landing)) >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id < sb.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!name b len. local_region ce es.scopes u name b len <=>
    local_region ce es.scopes s name b len` by
    (irule copy_buffer_local_region_frame >> qexists `sa` >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s` by metis_tac[] >>
  `!q. reserved q ==> eval_operand q u = eval_operand q s` by
    (rpt strip_tac >> first_x_assum irule >> fs[stage_resources_def] >> metis_tac[]) >>
  `stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s es sb u` by
    (irule stage_allocation_cont >> simp[]) >>
  qexistsl [`u`, `w`] >>
  simp[venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def] >> metis_tac[]
QED

Theorem stage_memory_value_allocation:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ sz < dimword (:256) /\
  vv_holds ce cx ty r vv es s /\ vv_at ce cx ty origin sa es r vv s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stage_cont ctx func cx lo prot staged reserved morig oorig rb
      ce env es sa s es sb u /\
    vv_holds ce cx ty r vv es u /\ vv_at ce cx ty origin sb es r vv u /\
    eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\ sa.cs_next_id < sb.cs_next_id /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!name b len. local_region ce es.scopes u name b len <=>
      local_region ce es.scopes s name b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p) /\
    (!v tv src. read_result cx r es = (INL v,es) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      eval_operand (vv_operand vv) u = SOME src /\
      (case vv of StackValue _ _ => ~is_word_type ty
        | LocatedValue _ p => p.ptr_location = LocMemory) /\
      val_footprint tv v <> 0 ==>
      regions_disjoint (w2n src) (val_footprint tv v) (w2n w) sz)
Proof
  strip_tac >> drule_all stage_memory_allocation_landing >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    metis_tac[] >>
  `vv_holds ce cx ty r vv es u` by
    (irule vv_holds_vars_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `vv_at ce cx ty origin sb es r vv u` by
    (irule held_vv_at_alloc_frame >> goal_assum (drule_at Any) >>
     fs[stage_cont_def, wb_frame_def] >> qexists `sa` >> simp[]) >>
  qexistsl [`u`, `w`] >> simp[] >> conj_tac
  >- metis_tac[] >> rpt strip_tac >>
  `stmt_state_rel ctx func ce cx es u /\ local_ptrs_reserved ce sa /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry)` by
    fs[stage_cont_def, stage_resources_def, wb_frame_def] >>
  `!name b len. local_region ce es.scopes s name b len ==>
    regions_disjoint (w2n w) sz b len` by metis_tac[] >>
  drule_all intcall_vv_at_allocation_disjoint >> simp[]
QED

Theorem stage_forcing_cont:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel ctx func ce cx es u /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above lo u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x u = SOME w) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!a k. prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
  (!n p k. local_region ce es.scopes u n p k <=>
    local_region ce es.scopes s n p k) /\
  (!aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\ aid < sa.cs_next_id /\
    (!n p z. local_region ce es.scopes s n p z ==> a+k <= p \/ p+z <= a) ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  locals_kept ce es es s u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s es sb u
Proof
  strip_tac >> simp[stage_cont_def] >> conj_tac
  >- (irule stage_resources_frame >> simp[] >>
      qexistsl [`s`, `sa`] >> simp[]) >>
  simp[wb_frame_def] >> metis_tac[]
QED
