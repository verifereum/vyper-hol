Theory assignEffectfulIndexPhysical
Ancestors
  immutableDeployPhysicalSource exprSimIfExpWidenedCounted
  aggregateEvaluatedLayout exprSimUnwrapProps context exprLowering
  loweringPosts valueCopyBytes vyperAST compileEnv exprSimConcatResult
  exprSimIfExpWidenedPhysicalType bodyMemSnapshotSourceLocation

Theorem snapshot_retag_unwrap:
  vv_holds ce cx t tv vv es s /\
  (pty = t \/ is_bytestring_type pty /\ is_bytestring_type t) /\
  (vv_location vv <> NONE /\ vv_location vv <> SOME LocMemory ==> pty = t) ==>
  unwrap_value ce (vv_with_type pty vv) = unwrap_value ce vv
Proof
  Cases_on `vv` >> simp[vv_with_type_def, unwrap_value_def] >>
  strip_tac >> gvs[vv_holds_def, vv_location_def] >>
  simp[is_bytestring_word_type] >>
  Cases_on `p.ptr_location = LocMemory` >> gvs[]
QED


Theorem snapshot_physical_unwrap_path:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  compile_expr ce ty e sc = (vv,se) /\
  unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) sm = (op,sb) /\
  local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?stv u. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
      ~is_word_type (post_value_type ce e) ==>
      type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
      type_memory_size tvt < 2 ** 64) /\
    gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    (is_word_type (lowered_value_type ce e) ==>
      eval_operand op u = SOME (typed_val_to_w256 stv v)) /\
    (~is_word_type (lowered_value_type ce e) ==>
      ?w. eval_operand op u = SOME w /\
        val_in_memory stv v (w2n w) u.vs_memory) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee s` by
    fs[vv_post_def] >>
  `(vv_location vv <> NONE /\ vv_location vv <> SOME LocMemory ==>
    lowered_value_type ce e = post_value_type ce e)` by
    metis_tac[snapshot_changed_type_location] >>
  `(post_value_type ce e <> expr_type e ==>
    ((?t op. vv = StackValue t op) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
       ~is_word_type t)))` by
    (strip_tac >> irule compile_changed_physical_unwrap_shape >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
     metis_tac[post_value_type_word, post_value_type_nonword]) >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) =
   unwrap_value ce vv` by
    (irule snapshot_retag_unwrap >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     metis_tac[immutable_rhs_post_physical_classify]) >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64` by
    metis_tac[body_post_type_allocation_bound] >>
  `unwrap_value ce vv sm = (op,sb)` by metis_tac[] >>
  drule_all immutable_rhs_physical_typed >> strip_tac >>
  drule_all unwrap_value_physical_path >> strip_tac >>
  qexistsl_tac [`stv`,`u`] >> simp[] >> conj_tac
  >- (strip_tac >>
      `post_value_type ce e = lowered_value_type ce e` by
        metis_tac[immutable_rhs_post_physical_classify, is_bytestring_word_type] >>
      gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  strip_tac >> drule_all immutable_rhs_physical_memory >> metis_tac[]
QED
