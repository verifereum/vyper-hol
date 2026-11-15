(* Turn the loop's robust memory and allocation coverage into the public
   pointer value/buffer posts.  Capacity is distinct from value footprint. *)
Theory bodyPtrMakeArrayPackage
Ancestors
  bodyPtrLiteralPackageCore bodyPtrPhysicalLiteralPackage
  bodyPtrMakeArrayTupleLoop bodyPtrDefs exprSimProps valueEncoding valueEncodingDefs
  venomState words ptrDiscipline bodyPtrMakeArrayAllocCursor
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayMaterialiseFrame
  bodyPtrMakeArrayExternalInstall loweringPosts exprSimAlloc emitHelperProps
  finite_map bodyPtrMakeArrayConsInvariant allocationPtr compileEnv loweringStateRelDefs
  gasSummaryComposePtr exprLowering exprLoweringProps
  exprSimAggregateEncoding exprSimAggregateSource vyperState argsTailPtr
  calldataReconstruction exprSimAggregateLayout exprSimHyps vyperTypeSystem
  exprSimHypsDefs allocLimits bodyPtrMakeArrayPositiveWord
  bodyPtrMakeArrayPrimitiveInstall

Theorem literal_empty_tuple_loop:
  compile_make_tuple compile_expr ce args (MAP expr_type args) (Var root) 0 sm = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  literal_loop_frame pure ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
    es sa s G tn es sm H tm a ([] : (type_value # value # num # num) list) 0 /\
  stmt_state_rel ctx func ce cx es s /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  (pure ==> ~EXISTS expr_has_effect args) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,a,H,tm)
    (\res ee H' tm' z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame pure ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
        es sa s G tn ee sb H' tm' z ([] ++ added) (0 + type_memory_size_list tvs) /\
      literal_prefix_ok ([] ++ added) tm' z /\
      (!m. mem_agree_outside tm'.t_mem z.vs_memory m ==> tuple_in_memory vs tvs (addr+0) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >> irule literal_tuple_loop_outcome_ptr >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem literal_allocated_tuple_outcome:
  compile_alloc_buffer (type_memory_size_list tvs) sa = (buf,sm) /\
  buf.buf_operand = Var root /\
  compile_make_tuple compile_expr ce args (MAP expr_type args) (Var root) 0 sm = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ type_memory_size_list tvs < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  (pure ==> ~EXISTS expr_has_effect args) ==>
  out = Var root /\
  ?addr. addr + type_memory_size_list tvs < dimword(:256) /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s,G,tn)
    (\res ee H tm z. ?vs cells. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      literal_loop_frame pure ctx func ce cx d root sa.cs_next_id addr (type_memory_size_list tvs)
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
  drule_all (Q.INST [`D` |-> `cx_dead cx`] (SPEC_ALL literal_allocated_loop_start)) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
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

Theorem literal_tuple_widened_vv_sim_ptr:
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) es /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  ann <> TupleT (MAP expr_type args) ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty (Builtin ann (MakeArray NONE bnd) args) es
Proof
  strip_tac >> mp_tac (SPEC_ALL literal_tuple_vv_sim_ptr_physical) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem literal_tuple_vv_sim_ptr:
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) es /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty (Builtin ann (MakeArray NONE bnd) args) es
Proof
  strip_tac >>
  reverse (Cases_on `ann = TupleT (MAP expr_type args)`)
  >- (drule_all literal_tuple_widened_vv_sim_ptr >> simp[]) >>
  gvs[] >> rw[expr_vv_sim_ptr_def] >>
  drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `type_memory_size_list tvs < dimword(:256)` by
    (`type_memory_bytes ce (TupleT (MAP expr_type args)) < 2 ** 64` by
       fs[expr_body_pre_def, alloc_limits_expr_def, type_alloc_ok_def,
          is_word_type_def] >>
     pop_assum mp_tac >>
     simp[Once type_memory_bytes_def, wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     qpat_x_assum `SUM _ = type_memory_size_list _` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  `?root. ba.buf_operand = Var root` by
    metis_tac[bodyPtrMakeArrayAllocBufferTheory.alloc_buffer_emitted] >>
  fs[exprLoweringTheory.tuple_literal_types_def] >>
  drule_all (REWRITE_RULE []
    (Q.INST [`pure` |-> `~EXISTS expr_has_effect args`]
      (SPEC_ALL literal_allocated_tuple_outcome))) >>
  disch_then (qspec_then `PG` strip_assume_tac) >> gvs[] >>
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
          listTheory.MAP_MAP_o, combinTheory.o_DEF] >> fs[listTheory.MAP_MAP_o, combinTheory.o_DEF]) >>
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
  literal_loop_frame pure ctx func ce cx d root sa.cs_next_id addr capacity
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
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  (pure ==> ~EXISTS expr_has_effect args) ==>
  out = Var root /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,a,H,tm)
    (\res ee H' tm' z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
      literal_loop_frame pure ctx func ce cx d root sa.cs_next_id addr capacity
        es sa s G tn ee sb H' tm' z (cells ++ added)
          ((if header then 32 else 0) + type_memory_size_list (REPLICATE (LENGTH args) tv)) /\
      literal_prefix_ok (cells ++ added) tm' z /\
      (!m. mem_agree_outside tm'.t_mem z.vs_memory m ==>
        tuple_in_memory vs (REPLICATE (LENGTH args) tv) (addr+(if header then 32 else 0)) m))
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >> irule literal_array_loop_outcome_ptr >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >> fs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >> metis_tac[]) >>
  (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`et`, `header`, `0`] >> simp[]
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
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  (pure ==> ~EXISTS expr_has_effect args) ==>
  out = Var root /\
  ?addr. addr + capacity < dimword(:256) /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx args) (es,s,G,tn)
    (\res ee H tm z. ?vs added. res = INL vs /\ expr_sim_inv ce cx env ee /\
      LIST_REL value_has_type (REPLICATE (LENGTH args) tv) vs /\
      literal_loop_frame pure ctx func ce cx d root sa.cs_next_id addr capacity
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
  drule_all (Q.INST [`D` |-> `cx_dead cx`] (SPEC_ALL literal_allocated_loop_start)) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
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

Theorem literal_array_widened_vv_sim_ptr:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  ~EVERY (\e. expr_type e = et) args ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty (Builtin ann (MakeArray (SOME et) bnd) args) es
Proof
  strip_tac >> mp_tac (SPEC_ALL literal_array_vv_sim_ptr_physical) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem literal_array_vv_sim_ptr:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es /\
  body_inv tops ctx ce cx /\ body_exprs_ptr_ok cx args /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  (!e. MEM e args ==> int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  expr_vv_sim_ptr d ctx PG func ce cx ty (Builtin ann (MakeArray (SOME et) bnd) args) es
Proof
  strip_tac >>
  reverse (Cases_on `EVERY (\e. expr_type e = et) args`)
  >- (drule_all literal_array_widened_vv_sim_ptr >> simp[]) >>
  rw[expr_vv_sim_ptr_def] >>
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
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`)
    (REWRITE_RULE [] (Q.INST [`pure` |-> `~EXISTS expr_has_effect args`]
      (SPEC_ALL literal_allocated_array_outcome))) >>
  simp[] >> disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  simp[type_memory_size_list_replicate] >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >> simp[] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`tops`, `env`] mp_tac) >> simp[] >>
  disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >> gvs[] >>
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
    disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
    simp[vyperASTTheory.expr_type_def] >>
    disch_then (drule_at (Pat `LIST_REL _ _ _`)) >> simp[] >>
    disch_then (qspec_then `[]` mp_tac) >> simp[contextTheory.mk_ptr_def]) >>
  gen_tac >> Cases_on `rr` >> simp[]
QED
