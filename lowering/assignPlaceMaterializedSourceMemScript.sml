(* Materialization frames destination operands at the unwrap frontier. *)
Theory assignPlaceMaterializedSourceMem
Ancestors
  assignPlaceMemoryContinuationMem bodyMemAssignAttrStorage
  stmtSimAugAssignPlaceMemory fragGasPathMem loweringPosts context venomState
  memoryLocalRhsProps valueCopyBytes compileEnv exprLoweringProps

Theorem assign_materialized_destination_frame:
  expr_post ctx func ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op u /\ gas_path_mem ctx func s n (OK u) /\
  (!x. dst = Var x ==> not_fresh_at sm x) /\
  eval_operand dst s = SOME w ==>
  eval_operand dst u = SOME w
Proof
  strip_tac >>
  `u.vs_labels = s.vs_labels` by
    metis_tac[gas_path_mem_exec, aug_place_path_labels] >>
  Cases_on `dst` >> gvs[eval_operand_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  first_x_assum irule >> gvs[not_fresh_at_def]
QED

Theorem assign_materialized_lowered_contents:
  (lt = et \/ is_bytestring_type et /\ is_bytestring_type lt /\ arg_type_fits lt et) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) lt = SOME stv /\ value_has_type stv v /\
  type_memory_bytes ce et = type_memory_size etv /\
  type_memory_bytes ce lt = type_memory_size stv /\
  val_in_memory etv v off s.vs_memory /\
  off + type_memory_size etv <= s.vs_alloca_next /\
  off + type_memory_size etv < dimword (:256) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
    regions_disjoint off (type_memory_size etv) b len) ==>
  val_in_memory stv v off s.vs_memory /\
  off + type_memory_size stv <= s.vs_alloca_next /\
  off + type_memory_size stv < dimword (:256) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
    regions_disjoint off (type_memory_size stv) b len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lt = et` >- (gvs[] >> metis_tac[]) >>
  `is_bytestring_type et /\ is_bytestring_type lt /\ arg_type_fits lt et`
    by metis_tac[] >>
  `type_memory_size stv <= type_memory_size etv` by
    metis_tac[arg_type_fits_bytestring_memory_bytes] >>
  `val_in_memory stv v off s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  simp[] >>
  rpt strip_tac >>
  first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac
QED

Theorem assign_storage_materialized_source_mem:
  post_value_type cenv e = expr_type e /\
  unwrap_value cenv (LocatedValue ty srcp) sm = (op,sb) /\
  (srcp.ptr_location = LocStorage \/ srcp.ptr_location = LocTransient) /\
  ~is_word_type ty /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. srcp.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty srcp) s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. dst = Var x ==> not_fresh_at sm x) /\ eval_operand dst s = SOME dw ==>
  ?z w tv. gas_path_mem ctx func s 0 (OK z) /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op z /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op z = SOME w /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    w2n w + type_memory_size tv < dimword (:256) /\
    w2n w + type_memory_size tv <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
    eval_operand dst z = SOME dw /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x z = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule vv_post_rebase_mem_src >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved cenv sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ ee _ _ _ _ _ _ _`)
    assign_storage_unwrap_endpoint_mem >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `eval_operand dst z = SOME dw` by
    (irule assign_materialized_destination_frame >> metis_tac[]) >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
     lookup_var x z = SOME w` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def] >> strip_tac >> rpt strip_tac >>
     first_x_assum irule >> gvs[not_fresh_at_def]) >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >> metis_tac[]
QED

Theorem assign_code_materialized_source_mem:
  post_value_type cenv e = expr_type e /\
  unwrap_value cenv (LocatedValue ty srcp) sm = (op,sb) /\
  srcp.ptr_location = LocCode /\
  ~is_word_type ty /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. srcp.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty srcp) s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. dst = Var x ==> not_fresh_at sm x) /\ eval_operand dst s = SOME dw ==>
  ?z w tv. gas_path_mem ctx func s 0 (OK z) /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op z /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op z = SOME w /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    w2n w + type_memory_size tv < dimword (:256) /\
    w2n w + type_memory_size tv <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
    eval_operand dst z = SOME dw /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x z = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule vv_post_rebase_mem_src >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved cenv sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ ee _ _ _ _ _ _ _`)
    assign_code_unwrap_endpoint_mem >>
  disch_then (qspecl_then [`sb`, `op`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `eval_operand dst z = SOME dw` by
    (irule assign_materialized_destination_frame >> metis_tac[]) >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
     lookup_var x z = SOME w` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def] >> strip_tac >> rpt strip_tac >>
     first_x_assum irule >> gvs[not_fresh_at_def]) >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >> metis_tac[]
QED
