(* Turn the loop's robust memory and allocation coverage into the public
   pointer value/buffer posts.  Capacity is distinct from value footprint. *)
Theory bodyPtrMakeArrayPackage
Ancestors
  bodyPtrMakeArrayTupleLoop bodyPtrDefs exprSimProps valueEncoding
  venomState words ptrDiscipline bodyPtrMakeArrayAllocCursor
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayMaterialiseFrame
  bodyPtrMakeArrayExternalInstall loweringPosts exprSimAlloc emitHelperProps
  finite_map bodyPtrMakeArrayConsInvariant allocationPtr compileEnv
  gasSummaryComposePtr exprLowering exprLoweringProps
  exprSimAggregateEncoding exprSimAggregateSource vyperState argsTailPtr
  calldataReconstruction

Theorem literal_memory_ptr_posts:
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_wf tv v /\ type_memory_size tv <= capacity /\
  type_memory_bytes ce (lowered_value_type ce e) <= capacity /\
  lookup_var root s = SOME (n2w addr) /\ addr < dimword(:256) /\
  FLOOKUP G root = SOME (addr,capacity) /\ op_taint tn (Var root) = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v addr m) ==>
  ptr_val_ok cx ty v (Var root) G tn s /\ ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  `val_store_size tv v <= capacity` by metis_tac[val_store_size_le, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, eval_operand_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.ADD_ASSOC]
QED

Theorem literal_allocated_loop_start:
  compile_alloc_buffer capacity sa = (buf,sm) /\ buf.buf_operand = Var root /\
  cs_extends sm sb /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  capacity < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?a H tm addr.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK a) /\
    addr + capacity < dimword(:256) /\
    literal_loop_frame ctx func ce cx d root sa.cs_next_id addr capacity
      es sa s G tn es sm H tm a ([] : (type_value # value # num # num) list) 0
Proof
  strip_tac >> drule_all allocated_fragment_install >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all (SRULE [] literal_alloc_buffer_cursor_run) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule literal_alloc_buffer_cursor_shape >> strip_tac >>
  `ghost_inv d ce cx es H tm a /\ ghost_kept ce es sa G tn s H tm` by
    (irule literal_allocated_copy_ghost_post >> simp[op_prov_def] >>
     conj_tac >- gvs[op_prov_def] >>
     conj_tac >- (qexistsl [`w2n w`, `capacity`, `a`] >> simp[arithmeticTheory.ADD_COMM] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- metis_tac[] >>
       qpat_x_assum `!i. _ ==> (i IN tm.t_mem <=> _)` mp_tac >>
       simp[arithmeticTheory.ADD_COMM]) >>
     metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
      pairTheory.SND, exprLoweringPropsTheory.ci_mono_def] >>
  `!name b len. local_region ce es.scopes s name b len ==>
     regions_disjoint (w2n w) capacity b len` by
    metis_tac[exprSimPtrLiteralBufferTheory.literal_ptr_local_region_frame] >>
  qexistsl [`a`, `H`, `tm`, `w2n w`] >> simp[] >>
  gvs[literal_loop_frame_def, wb_frame_def, locals_kept_def,
    regions_disjoint_def, eval_operand_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem literal_loop_vv_post:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s0 G0 tn0 ee sb G tn s (cells : (type_value # value # num # num) list) off /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ val_wf tv v /\
  val_footprint tv v <= capacity /\ addr < dimword(:256) /\
  val_in_memory tv v addr s.vs_memory ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) s
Proof
  strip_tac >>
  fs[literal_loop_frame_def] >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, contextTheory.mk_ptr_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    eval_operand_def] >>
  reverse conj_tac >- (fs[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexistsl [`aid`, `addr`, `capacity`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name p k. local_region ce ee.scopes s name p k ==> _`
    (drule_then mp_tac) >> decide_tac
QED

Theorem literal_loop_pointer_posts:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s0 G0 tn0 ee sb G tn s (cells : (type_value # value # num # num) list) off /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ val_wf tv v /\
  type_memory_size tv <= capacity /\ addr < dimword(:256) /\
  type_memory_bytes ce (lowered_value_type ce e) <= capacity /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v addr m) ==>
  ptr_vv_ok cx (expr_type e) (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) ee G tn s /\
  ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by
    fs[literal_loop_frame_def, ptr_covers_def] >>
  `ptr_val_ok cx (expr_type e) v (Var root) G tn s /\
   ptr_buf_ok ce e (Var root) G s` by
    (irule literal_memory_ptr_posts >>
     fs[literal_loop_frame_def] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[ptr_vv_ok_def, contextTheory.mk_ptr_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  fs[ptr_val_ok_def]
QED


Theorem literal_empty_tuple_loop:
  compile_make_tuple compile_expr ce args (Var root) 0 sm = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
    es sa s G tn es sm H tm a ([] : (type_value # value # num # num) list) 0 /\
  stmt_state_rel ctx func ce cx es s /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,a,H,tm)
    (\res ee H' tm' z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
        es sa s G tn ee sb H' tm' z ([] ++ added) (0 + type_memory_size_list tvs) /\
      literal_prefix_ok ([] ++ added) tm' z /\
      (!m. mem_agree_outside tm'.t_mem z.vs_memory m ==> tuple_in_memory vs tvs (addr+0) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >> irule literal_tuple_loop_outcome_ptr >>
  goal_assum (drule_at Any) >> simp[] >> qexists `sm` >> simp[]
QED

Theorem literal_allocated_tuple_outcome:
  compile_alloc_buffer (type_memory_size_list tvs) sa = (buf,sm) /\
  buf.buf_operand = Var root /\
  compile_make_tuple compile_expr ce args (Var root) 0 sm = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ type_memory_size_list tvs < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  out = Var root /\
  ?addr. addr + type_memory_size_list tvs < dimword(:256) /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s,G,tn)
    (\res ee H tm z. ?vs cells. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
        es sa s G tn ee sb H tm z cells (type_memory_size_list tvs) /\
      literal_prefix_ok cells tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==> tuple_in_memory vs tvs addr m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all literal_allocated_loop_start >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  drule_all literal_empty_tuple_loop >> strip_tac >>
  simp[] >> qexists `addr` >> simp[] >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >> fs[]
QED

(* S1's action equation is local to exprSimAggregates. *)
Theorem literal_tuple_action:
  compatible_bound bnd (LENGTH args) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) args) =
  bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (TupleV vs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >>
  drule_all aggregate_eval_make_tuple >>
  disch_then (qspec_then `ann` mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem literal_tuple_endpoint_posts:
  literal_loop_frame ctx func ce cx d root aid addr (type_memory_size_list tvs)
    es sa s0 G0 tn0 ee sb G tn s (cells : (type_value # value # num # num) list) off /\
  expr_type e = TupleT tys /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (TupleTV tvs) /\
  type_memory_bytes ce (lowered_value_type ce e) <= type_memory_size_list tvs /\
  addr < dimword(:256) /\ LIST_REL value_has_type tvs vs /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> tuple_in_memory vs tvs addr m) ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value (ArrayV (TupleV vs)))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) s /\
  ptr_vv_ok cx (expr_type e) (Value (ArrayV (TupleV vs)))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) ee G tn s /\
  ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >>
  `tuple_in_memory vs tvs addr s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all calldata_tuple_values_typed_memory >> strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) addr m` by
    simp[val_in_memory_def] >>
  conj_tac
  >- (irule literal_loop_vv_post >> simp[is_word_type_def] >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[val_footprint_le, type_memory_size_def]) >>
  irule literal_loop_pointer_posts >> simp[is_word_type_def] >>
  goal_assum (drule_at Any) >> simp[type_memory_size_def] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
