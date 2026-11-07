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
  calldataReconstruction exprSimAggregateLayout exprSimHyps vyperTypeSystem
  exprSimHypsDefs allocLimits bodyPtrMakeArrayPositiveWord
  bodyPtrMakeArrayPrimitiveInstall

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


Theorem literal_tuple_vv_sim_ptr:
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty (Builtin ann (MakeArray NONE bnd) args) es
Proof
  strip_tac >> rw[expr_vv_sim_ptr_def] >>
  drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `type_memory_size_list tvs < dimword(:256)` by
    (fs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `?root. ba.buf_operand = Var root` by
    metis_tac[bodyPtrMakeArrayAllocBufferTheory.alloc_buffer_emitted] >>
  fs[] >> drule_all literal_allocated_tuple_outcome >> strip_tac >> gvs[] >>
  simp[literal_tuple_action, combinTheory.o_DEF] >>
  drule (gas_outcome_ptr_return_map
    |> Q.GEN `f` |> Q.ISPEC `\(vs : value list). Value (ArrayV (TupleV vs))`
    |> REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]) >>
  disch_then (match_mp_tac o BETA_RULE) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule literal_loop_frame_runtime >> strip_tac >>
      `addr < dimword(:256)` by decide_tac >>
      `type_memory_bytes ce (lowered_value_type ce
         (Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args)) <=
         type_memory_size_list tvs` by
        (simp[lowered_value_type_def, vyperASTTheory.expr_type_def, type_memory_bytes_def,
          listTheory.MAP_MAP_o, combinTheory.o_DEF] >> fs[combinTheory.o_DEF]) >>
      drule_at (Pat `type_memory_bytes _ _ <= _`) literal_tuple_endpoint_posts >>
      simp[vyperASTTheory.expr_type_def] >>
      disch_then drule >> simp[] >>
      disch_then drule >> simp[contextTheory.mk_ptr_def]) >>
  gen_tac >> Cases_on `rr` >> simp[]
QED

Theorem literal_empty_array_loop:
  compile_make_array_elems compile_expr ce args et (type_memory_bytes ce et)
    header (Var root) 0 sm = (out,sb) /\
  EVERY (\e. expr_type e = et) args /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame ctx func ce cx d root sa.cs_next_id addr capacity
    es sa s G tn es sm H tm a (cells : (type_value # value # num # num) list)
      (if header then 32 else 0) /\
  literal_prefix_ok cells tm a /\
  (if header then 32 else 0) + type_memory_size_list (REPLICATE (LENGTH args) tv) <= capacity /\
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
      LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
      literal_loop_frame ctx func ce cx d root sa.cs_next_id addr capacity
        es sa s G tn ee sb H' tm' z (cells ++ added)
          ((if header then 32 else 0) + type_memory_size_list (REPLICATE (LENGTH args) tv)) /\
      literal_prefix_ok (cells ++ added) tm' z /\
      (!m. mem_agree_outside tm'.t_mem z.vs_memory m ==>
        tuple_in_memory vs (REPLICATE (LENGTH args) tv) (addr+(if header then 32 else 0)) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >> irule literal_array_loop_outcome_ptr >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`et`, `header`, `0`] >> simp[]
QED

Theorem literal_array_header_start:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s G tn es sm H tm a ([] : (type_value # value # num # num) list) 0 /\
  emit_void MSTORE [Var root; Lit (n2w n)] sm = ((),sn) /\
  fn_has_code sm sn func /\ 32 <= capacity /\
  addr < dimword(:256) /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor ==>
  ?z tm'. gas_path_ptr D 0 ctx func PG H tm a 0 H tm' (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      es sa s G tn es sn H tm' z [(BaseTV (UintT 256),IntV (&(n MOD dimword(:256))),addr,32)] 32 /\
    literal_prefix_ok [(BaseTV (UintT 256),IntV (&(n MOD dimword(:256))),addr,32)] tm' z
Proof
  strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  drule (REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO] literal_word_loop_store) >>
  simp[] >> disch_then irule >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  fs[ci_mono_def, val_footprint_def, type_memory_size_def, val_wf_def, vyperTypingTheory.value_has_type_def,
     wordsTheory.dimword_def] >>
  conj_tac
  >- (qexists `BaseT (UintT 256)` >>
      simp[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  qexistsl [`n2w addr`, `root`, `sm.cs_next_id`, `Lit (n2w n)`] >>
  simp[eval_operand_def, op_taint_def, typed_val_to_w256_def,
       w2n_n2w] >>
  fs[wordsTheory.dimword_def, val_to_w256_def, literal_loop_frame_def] >>
  simp[integer_wordTheory.i2w_pos, wordsTheory.n2w_mod, wordsTheory.dimword_def] >>
  fs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac
QED

Theorem literal_array_prepare:
  compile_make_array compile_expr ce args et (type_memory_bytes ce et) header (Var root) sm = (out,sb) /\
  EVERY (\e. expr_type e = et) args /\
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s G tn es sm H tm a ([] : (type_value # value # num # num) list) 0 /\
  fn_has_code sm sb func /\ (header ==> 32 <= capacity) /\
  addr < dimword(:256) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor ==>
  ?sn z tm'.
    compile_make_array_elems compile_expr ce args et (type_memory_bytes ce et) header (Var root) 0 sn = (out,sb) /\
    ci_mono sm sn /\ ci_mono sn sb /\
    gas_path_ptr D 0 ctx func PG H tm a 0 H tm' (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      es sa s G tn es sn H tm' z
        (if header then [(BaseTV (UintT 256),IntV (&(LENGTH args MOD dimword(:256))),addr,32)] else [])
        (if header then 32 else 0) /\
    literal_prefix_ok
      (if header then [(BaseTV (UintT 256),IntV (&(LENGTH args MOD dimword(:256))),addr,32)] else []) tm' z
Proof
  strip_tac >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_array_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      qexistsl [`sm`, `a`, `tm`] >> simp[] >>
      conj_tac >- simp[ci_mono_def, cs_extends_refl] >>
      irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >>
      fs[literal_loop_frame_def]) >>
  Cases_on `emit_void MSTORE [Var root; Lit (n2w (LENGTH args))] sm` >>
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def] >>
  rename1 `emit_void _ _ sm = ((),sn)` >>
  drule exprSimAggregateLoopsTheory.compile_make_array_elems_as_tuple >>
  disch_then (qspecl_then [`T`, `compile_expr`, `ce`, `Var root`, `0`] assume_tac) >>
  `ci_mono sn sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `fn_has_code sm sn func` by metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  drule_all literal_array_header_start >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`sn`, `z`, `tm'`] >> simp[]
QED

Theorem literal_allocated_array_outcome:
  compile_alloc_buffer capacity sa = (buf,sm) /\ buf.buf_operand = Var root /\
  compile_make_array compile_expr ce args et (type_memory_bytes ce et) header (Var root) sm = (out,sb) /\
  EVERY (\e. expr_type e = et) args /\ evaluate_type (get_tenv cx) et = SOME tv /\
  (if header then 32 else 0) + type_memory_size_list (REPLICATE (LENGTH args) tv) <= capacity /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ capacity < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  out = Var root /\
  ?addr. addr + capacity < dimword(:256) /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s,G,tn)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
      literal_loop_frame ctx func ce cx d root sa.cs_next_id addr capacity
        es sa s G tn ee sb H tm z
          ((if header then [(BaseTV (UintT 256),IntV (&(LENGTH args MOD dimword(:256))),addr,32)] else []) ++ added)
          ((if header then 32 else 0) + type_memory_size_list (REPLICATE (LENGTH args) tv)) /\
      literal_prefix_ok
        ((if header then [(BaseTV (UintT 256),IntV (&(LENGTH args MOD dimword(:256))),addr,32)] else []) ++ added) tm z /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        tuple_in_memory vs (REPLICATE (LENGTH args) tv) (addr+(if header then 32 else 0)) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_array_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all literal_allocated_loop_start >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `header ==> 32 <= capacity` by (Cases_on `header` >> gvs[] >> decide_tac) >>
  `addr < dimword(:256)` by decide_tac >>
  drule_all literal_array_prepare >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `fn_has_code sn sb func` by metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sn p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sn p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  drule_all literal_empty_array_loop >> strip_tac >>
  simp[] >> qexists `addr` >> simp[] >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  fs[arithmeticTheory.ADD_COMM]
QED

Theorem literal_array_memory_posts:
  compatible_bound bnd n /\ LIST_REL value_has_type (REPLICATE n tv) vs /\
  literal_prefix_ok
    ((if (case bnd of Dynamic _ => T | _ => F) then
       [(BaseTV (UintT 256),IntV (&(n MOD dimword(:256))),addr,32)] else []) ++ cells) tn s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    tuple_in_memory vs (REPLICATE n tv)
      (addr+(if (case bnd of Dynamic _ => T | _ => F) then 32 else 0)) m) ==>
  val_wf (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs)) addr m)
Proof
  strip_tac >>
  `LENGTH vs = n` by metis_tac[listTheory.LIST_REL_LENGTH, rich_listTheory.LENGTH_REPLICATE] >>
  `EVERY (value_has_type tv) vs` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `LENGTH vs = n` (SUBST1_TAC o SYM) >>
     qid_spec_tac `vs` >> Induct >> simp[listTheory.LIST_REL_def, rich_listTheory.REPLICATE]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    elems_in_memory vs (addr+(if (case bnd of Dynamic _ => T | _ => F) then 32 else 0)) tv m` by
    metis_tac[tuple_in_memory_replicate_elems] >>
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by simp[mem_agree_outside_def] >>
  Cases_on `bnd`
  >- (gvs[vyperValueTheory.compatible_bound_def] >>
      conj_tac
      >- metis_tac[calldata_fixed_values_typed_memory] >>
      metis_tac[calldata_fixed_values_typed_memory]) >>
  gvs[vyperValueTheory.compatible_bound_def, literal_prefix_cell] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> mem_word_at addr m = n2w (LENGTH vs)` by
    (rpt strip_tac >>
     qpat_x_assum `!m. _ ==> val_in_memory _ _ _ _` drule >>
     simp[val_in_memory_def, val_to_w256_def, integer_wordTheory.i2w_pos, wordsTheory.n2w_mod]) >>
  conj_tac
  >- metis_tac[calldata_dynamic_values_typed_memory] >>
  metis_tac[calldata_dynamic_values_typed_memory]
QED

Theorem literal_array_endpoint_posts:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    es sa s0 G0 tn0 ee sb G tn s (cells : (type_value # value # num # num) list) off /\
  expr_type e = ArrayT et bnd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV tv bnd) /\
  capacity = type_memory_size (ArrayTV tv bnd) /\
  type_memory_bytes ce (lowered_value_type ce e) <= capacity /\
  addr < dimword(:256) /\ compatible_bound bnd n /\
  LIST_REL value_has_type (REPLICATE n tv) vs /\
  literal_prefix_ok
    ((if (case bnd of Dynamic _ => T | _ => F) then
       [(BaseTV (UintT 256),IntV (&(n MOD dimword(:256))),addr,32)] else []) ++ added) tn s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    tuple_in_memory vs (REPLICATE n tv)
      (addr+(if (case bnd of Dynamic _ => T | _ => F) then 32 else 0)) m) ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value (ArrayV (make_array_value tv bnd vs)))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) s /\
  ptr_vv_ok cx (expr_type e) (Value (ArrayV (make_array_value tv bnd vs)))
    (LocatedValue (expr_type e) (mk_ptr (Var root) LocMemory)) ee G tn s /\
  ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >> drule_all literal_array_memory_posts >> strip_tac >>
  `val_in_memory (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs)) addr s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac
  >- (irule literal_loop_vv_post >> simp[is_word_type_def] >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[val_footprint_le]) >>
  irule literal_loop_pointer_posts >> simp[is_word_type_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem literal_array_action:
  compatible_bound bnd (LENGTH args) /\ evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args) =
  bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >>
  drule_all aggregate_eval_make_array >>
  disch_then (qspec_then `ann` mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem literal_array_vv_sim_ptr:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty (Builtin ann (MakeArray (SOME et) bnd) args) es
Proof
  strip_tac >> rw[expr_vv_sim_ptr_def] >>
  drule compile_array_literal_inv >> strip_tac >> gvs[] >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `type_memory_bytes ce (ArrayT et bnd) < dimword(:256)` by
    (fs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `?root. ba.buf_operand = Var root` by
    metis_tac[bodyPtrMakeArrayAllocBufferTheory.alloc_buffer_emitted] >> fs[] >>
  `compile_make_array compile_expr ce args et (type_memory_bytes ce et)
     (case bnd of Dynamic _ => T | _ => F) (Var root) sm = (u,sb)` by metis_tac[] >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) literal_allocated_array_outcome >>
  simp[] >> disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  simp[type_memory_size_list_replicate] >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >> simp[] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  `eval_expr cx (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) =
     bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))` by
    (irule literal_array_action >> simp[]) >>
  simp[combinTheory.o_DEF] >>
  drule (gas_outcome_ptr_return_map
    |> Q.GEN `f` |> Q.ISPEC `\(vs : value list). Value (ArrayV (make_array_value tv bnd vs))`
    |> REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]) >>
  disch_then (qspecl_then [`tv`, `bnd`] mp_tac) >>
  disch_then (match_mp_tac o BETA_RULE) >>
  conj_tac >- (rpt strip_tac >> gvs[] >>
    drule literal_loop_frame_runtime >> strip_tac >>
    `addr < dimword(:256)` by decide_tac >>
    `type_memory_bytes ce (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
      metis_tac[expr_sim_inv_memory_size] >>
    `type_memory_bytes ce (lowered_value_type ce
      (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args)) <= type_memory_bytes ce (ArrayT et bnd)` by
      simp[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
    drule_at (Pat `type_memory_bytes _ (lowered_value_type _ _) <= _`) literal_array_endpoint_posts >>
    disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
    simp[vyperASTTheory.expr_type_def] >>
    disch_then (drule_at (Pat `LIST_REL _ _ _`)) >> simp[] >>
    disch_then (qspec_then `[]` mp_tac) >> simp[contextTheory.mk_ptr_def]) >>
  gen_tac >> Cases_on `rr` >> simp[]
QED
