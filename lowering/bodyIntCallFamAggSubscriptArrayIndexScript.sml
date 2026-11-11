(* Transport of the captured array across a counted index evaluation. *)
Theory bodyIntCallFamAggSubscriptArrayIndex
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore
  exprSimSubscriptArrayEndpoint exprSimSubscriptArrayCompose
  exprSimSubscriptArrayFrame loweringPosts exprBopSimProps context
  exprLoweringProps compileEnv

Theorem intcall_framed_array_index_endpoint:
  intcall_expr_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 t sb u /\
  intcall_expr_cont fp ce env t sb u ee sc s /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sb s0 t r
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx t sb sc u ee iv iop s /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  is_word_type (expr_type idx) /\
  ((~ce.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sb /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id ==>
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sc s0 ee r
    (LocatedValue (ArrayT et bd) p) s /\
  intcall_expr_cont fp ce env es sa s0 ee sc s /\
  (!w. eval_operand p.ptr_operand u = SOME w ==> eval_operand p.ptr_operand s = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\
   expr_sim_inv ce fp.jc_cx env t /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee s` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  conj_tac
  >- (irule framed_array_base_endpoint >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> qexists_tac `env` >> simp[]) >>
  conj_tac
  >- (irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule eval_operand_frame >> simp[] >>
  qexistsl_tac [`sb`,`u`] >>
  fs[intcall_expr_cont_def] >> metis_tac[]
QED
