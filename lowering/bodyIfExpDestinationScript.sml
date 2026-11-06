Theory bodyIfExpDestination
Ancestors
  bodyMemAssignAttrStorage exprSimMemUnwrap loweringPosts freshWrites
  venomState compileEnv exprLowering exprSimIfExp exprSimVVFrame exprSimAlloc
  bodyMemAggregateUnwrap exprSimProps exprLoweringProps exprSimUnwrapProps
  exprSimMemDefs vyperInterpreter vyperState

Theorem ifexp_destination_through_post[local]:
  expr_post ctx func ce cx e ee (origin with cs_next_var := sm.cs_next_var)
    sn r ee v src u /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst r = SOME d /\
  FLOOKUP r.vs_allocas aid = SOME (w2n d,cap) ==>
  eval_operand dst u = SOME d /\
  FLOOKUP u.vs_allocas aid = SOME (w2n d,cap)
Proof
  strip_tac >> conj_tac
  >- (irule expr_post_rebased_operand_mem_src >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  fs[expr_post_def] >> metis_tac[]
QED

Theorem ifexp_allocated_post[local]:
  compile_alloc_buffer cap sa = (buf,sm) /\ fn_has_code sa sm func /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ cap < dimword (:256) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sm) s = OK q /\
  r = q with vs_inst_idx := LENGTH sm.cs_current_insts ==>
  vv_post ctx func ce cx e es origin sm s0 ee raw vv r
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all ifexp_alloc_preserves_post >> strip_tac >>
  gvs[vv_post_inst_idx]
QED

Theorem ifexp_allocate_path[local]:
  compile_alloc_buffer cap sa = (buf,sm) /\ fn_has_code sa sm func /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ cap < dimword (:256) /\
  eval_operand (vv_operand vv) s = SOME a /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r d. gas_path_mem ctx func s 0 (OK r) /\
    vv_post ctx func ce cx e es origin sm s0 ee raw vv r /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv r /\
    eval_operand buf.buf_operand r = SOME d /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n d,cap) /\
    w2n d + cap < dimword (:256) /\ w2n d + cap <= r.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes r name b len ==>
       regions_disjoint (w2n d) cap b len) /\
    (?x. buf.buf_operand = Var x /\ not_fresh_at sm x) /\
    alloca_history func r /\ s.vs_alloca_next <= r.vs_alloca_next /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `vv_post ctx func ce cx e es origin sm s0 ee raw vv u` by
    (irule ifexp_allocated_post >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv u` by
    (irule vv_store_bound_frame_mem_src >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`u`,`w`] >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem ifexp_unwrap_destination[local]:
  unwrap_value ce vv sm = (src,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sm /\
  origin.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (expr_type e) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  vv_post ctx func ce cx e es origin sm s0 ee (Value v) vv r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv r /\
  alloca_history func r /\ ~r.vs_halted /\
  r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst r = SOME d /\
  FLOOKUP r.vs_allocas aid = SOME (w2n d,cap) /\
  (!name b len. local_region ce ee.scopes r name b len ==>
     regions_disjoint (w2n d) cap b len) ==>
  ?u. gas_path_mem ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e ee (origin with cs_next_var := sm.cs_next_var)
      sn r ee v src u /\
    expr_store_bound cx (expr_type e) v src u /\
    eval_operand dst u = SOME d /\
    FLOOKUP u.vs_allocas aid = SOME (w2n d,cap) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
       regions_disjoint (w2n d) cap b len) /\
    alloca_history func u /\ r.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >>
  drule vv_post_rebase_mem_src >> strip_tac >>
  `local_ptrs_reserved ce (origin with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved ce sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ es _ _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_unwrap_value_path_mem_capacity >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  `eval_operand dst u = SOME d /\
   FLOOKUP u.vs_allocas aid = SOME (w2n d,cap)` by
    (irule ifexp_destination_through_post >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `u` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `name` >>
  irule local_region_frame >> conj_tac
  >- (qexists_tac `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`origin with cs_next_var := sm.cs_next_var`, `ee.scopes`, `u`] >>
  simp[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def]
QED

Theorem ifexp_allocate_unwrap_path:
  compile_alloc_buffer cap sa = (buf,sm) /\ fn_has_code sa sm func /\
  unwrap_value ce vv sm = (src,sn) /\ fn_has_code sm sn func /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sm.cs_next_var /\
  origin.cs_next_id <= sm.cs_next_id /\ cap < dimword (:256) /\
  eval_operand (vv_operand vv) s = SOME a /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  ~is_word_type (expr_type e) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r u d. gas_path_mem ctx func s 0 (OK r) /\
    gas_path_mem ctx func r 0 (OK u) /\
    vv_post ctx func ce cx e es origin sm s0 ee raw vv r /\
    expr_post ctx func ce cx e ee (origin with cs_next_var := sm.cs_next_var)
      sn r ee v src u /\
    expr_store_bound cx (expr_type e) v src u /\
    eval_operand buf.buf_operand u = SOME d /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n d,cap) /\
    w2n d + cap < dimword (:256) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
       regions_disjoint (w2n d) cap b len) /\
    (?x. buf.buf_operand = Var x /\ not_fresh_at sm x) /\
    alloca_history func r /\ alloca_history func u /\
    s.vs_alloca_next <= r.vs_alloca_next /\ r.vs_alloca_next <= u.vs_alloca_next /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >> drule_all ifexp_allocate_path >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK r)` >>
  `vv_post ctx func ce cx e es origin sm s0 ee (Value v) vv r` by
    metis_tac[vv_post_read_result] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv r` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ r` mp_tac >>
     rw[vv_store_bound_def] >> gvs[read_result_def, return_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) ifexp_unwrap_destination >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`buf.buf_operand`, `d`, `cap`, `sa.cs_next_id`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`r`,`u`,`d`] >> simp[] >> first_assum ACCEPT_TAC
QED
