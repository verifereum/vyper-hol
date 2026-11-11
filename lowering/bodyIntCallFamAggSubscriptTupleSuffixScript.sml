(* Readonly tuple selection: one endpoint for representation and resources. *)
Theory bodyIntCallFamAggSubscriptTupleSuffix
Ancestors
  bodyIntCallFamAggSubscriptTupleSource bodyIntCallFamAggSubscriptScratch
  exprSimVVFrame exprSimProps exprLoweringProps venomState
  emitHelperProps bodyIntCallJointContract compileEnv exprSimTuple
  bodyIntCallFamAggSubscriptTuple exprSimAttributeFields loweringPosts context vyperAST

Theorem intcall_vv_post_readonly_cursor:
  vv_post ctx func ce cx e es sa sm s0 ee tv vv t /\
  (u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) = t /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) t /\
  (!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  local_ptrs_reserved ce sa /\ sm.cs_next_id <= sb.cs_next_id /\
  stmt_state_rel ctx func ce cx ee u ==>
  vv_post ctx func ce cx e es sa sb s0 ee tv vv u
Proof
  strip_tac >>
  `vv_post ctx func ce cx e es sa sb s0 ee tv vv
     (u with vs_inst_idx := t.vs_inst_idx)` suffices_by simp[] >>
  irule vv_post_vars_frame >> simp[stmt_state_rel_inst_idx] >>
  qexistsl_tac [`t`, `sm`] >>
  simp[eval_operand_def, lookup_var_def, stmt_state_rel_inst_idx] >>
  fs[venom_state_component_equality, lookup_var_def]
QED

Theorem intcall_tuple_add_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es sa s0 ee sm t /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sm s0 ee tv bvv t /\
  post_value_type ce obj = TupleT tys /\ expr_type obj = TupleT tys /\
  expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  OPT_MMAP (evaluate_type (get_tenv fp.jc_cx)) tys = SOME tvs /\
  evaluate_type (get_tenv fp.jc_cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\ read_result fp.jc_cx tv ee = (INL (ArrayV (TupleV vs)),ee) /\
  values_have_types tvs vs /\ read_result fp.jc_cx selected ee = (INL (EL k vs),ee) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))]
    sm = (dst,sb) /\ fn_has_code sm sb fp.jc_func ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s0 ee sb u /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sb s0 ee tv bvv u /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript (EL k tys) obj idx)
      es sa sb s0 ee selected (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
    eval_operand (vv_operand bvv) u = SOME w /\
    eval_operand dst u = SOME (w + n2w (tuple_offset ce tys (vv_loc bvv) k)) /\
    (!x. dst = Var x ==> not_fresh_at sb x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))) t =
    SOME (n2w (tuple_offset ce tys (vv_loc bvv) k))` by simp[eval_operand_def] >>
  drule_all intcall_emit_add_cont >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es sa s0 ee sb u` >>
  `eval_operand (vv_operand bvv) u = SOME w` by
    (Cases_on `vv_operand bvv` >> gvs[eval_operand_def] >>
     fs[venom_state_component_equality] >> metis_tac[]) >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sb s0 ee tv bvv u` by
    (irule intcall_vv_post_readonly_cursor >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >>
     fs[not_fresh_at_def] >> metis_tac[]) >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript (EL k tys) obj idx)
      es sa sb s0 ee selected (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u` by
    (irule tuple_vv_post >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `u` >> simp[]
QED

Theorem intcall_tuple_selected_post:
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Subscript (EL k tys) obj idx)
    es sa sb s0 ee selected (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
  vv_at ce fp.jc_cx (TupleT tys) sa sb ee tv bvv u /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env es /\
  intcall_expr_cont fp ce env es sa s0 ee sb u /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  read_result fp.jc_cx tv ee = (INL (ArrayV (TupleV vs)),ee) /\
  OPT_MMAP (evaluate_type (get_tenv fp.jc_cx)) tys = SOME tvs /\
  evaluate_type (get_tenv fp.jc_cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\ eval_operand (vv_operand bvv) u = SOME w /\
  eval_operand dst u = SOME (w + n2w (tuple_offset ce tys (vv_loc bvv) k)) /\
  (vv_loc bvv = LocMemory ==>
    ?a len. a <= w2n w /\ w2n w + type_memory_size (TupleTV tvs) <= a + len /\
      a + len < dimword (:256) /\
      (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)) ==>
  ?tv. INL selected = INL tv /\
    vv_holds ce fp.jc_cx (post_value_type ce (Subscript (EL k tys) obj idx)) tv
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) ee u /\
    vv_at ce fp.jc_cx (post_value_type ce (Subscript (EL k tys) obj idx)) sa sb ee tv
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
    (post_value_type ce (Subscript (EL k tys) obj idx) <> expr_type (Subscript (EL k tys) obj idx) ==>
      vv_own ce fp.jc_cx (post_value_type ce (Subscript (EL k tys) obj idx)) sa sb ee tv
        (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u) /\
    (~expr_has_effect (Subscript (EL k tys) obj idx) ==>
      vv_storage_live fp.jc_cx (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) ee u) /\
    (!x. vv_operand (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) = Var x ==> not_fresh_at sb x) /\
    (post_value_type ce (Subscript (EL k tys) obj idx) <> NoneT /\
     ~is_word_type (post_value_type ce (Subscript (EL k tys) obj idx)) /\
     ~is_bytestring_type (post_value_type ce (Subscript (EL k tys) obj idx)) /\
     (mk_ptr dst (vv_loc bvv)).ptr_location = LocMemory ==>
     !etv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (Subscript (EL k tys) obj idx)) = SOME etv ==>
       ?cw a len. eval_operand (vv_operand (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv)))) u = SOME cw /\
         a <= w2n cw /\ w2n cw + type_memory_size etv <= a + len /\
         a + len < dimword (:256) /\
         (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)) /\
    intcall_expr_cont fp ce env es sa s0 ee sb u
Proof
  strip_tac >>
  fs[vv_post_def, vv_operand_def, mk_ptr_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >>
  `LENGTH tvs = LENGTH tys` by
    fs[vyperMiscTheory.OPT_MMAP_SOME_IFF] >>
  `k < LENGTH tys` by fs[] >>
  `evaluate_type (get_tenv fp.jc_cx) (EL k tys) = SOME (EL k tvs)` by
    (drule_all opt_mmap_el >> simp[]) >>
  gvs[] >>
  `?cw. eval_operand dst u = SOME cw /\
    a <= w2n cw /\ w2n cw + type_memory_size (EL k tvs) <= a + len /\
    a + len < dimword (:256) /\
    (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)` by
    (irule intcall_tuple_element_window >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`a`, `len`] >> gvs[] >> metis_tac[]
QED

Theorem intcall_tuple_suffix_post:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es sa s0 ee sm t /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sm s0 ee tv bvv t /\
  post_value_type ce obj = TupleT tys /\ expr_type obj = TupleT tys /\
  expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand bvv = Var x ==> not_fresh_at sm x) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  OPT_MMAP (evaluate_type (get_tenv fp.jc_cx)) tys = SOME tvs /\
  evaluate_type (get_tenv fp.jc_cx) (TupleT tys) = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\ read_result fp.jc_cx tv ee = (INL (ArrayV (TupleV vs)),ee) /\
  values_have_types tvs vs /\ read_result fp.jc_cx selected ee = (INL (EL k vs),ee) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))]
    sm = (dst,sb) /\ fn_has_code sm sb fp.jc_func /\
  (vv_loc bvv = LocMemory ==>
    ?a len. a <= w2n w /\ w2n w + type_memory_size (TupleTV tvs) <= a + len /\
      a + len < dimword (:256) /\
      (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    ?tv'. INL selected = INL tv' /\
    vv_holds ce fp.jc_cx (post_value_type ce (Subscript (EL k tys) obj idx)) tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) ee u /\
    vv_at ce fp.jc_cx (post_value_type ce (Subscript (EL k tys) obj idx)) sa sb ee tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
    (post_value_type ce (Subscript (EL k tys) obj idx) <> expr_type (Subscript (EL k tys) obj idx) ==>
      vv_own ce fp.jc_cx (post_value_type ce (Subscript (EL k tys) obj idx)) sa sb ee tv'
        (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u) /\
    (~expr_has_effect (Subscript (EL k tys) obj idx) ==>
      vv_storage_live fp.jc_cx (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) ee u) /\
    (!x. vv_operand (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) = Var x ==> not_fresh_at sb x) /\
    (post_value_type ce (Subscript (EL k tys) obj idx) <> NoneT /\
     ~is_word_type (post_value_type ce (Subscript (EL k tys) obj idx)) /\
     ~is_bytestring_type (post_value_type ce (Subscript (EL k tys) obj idx)) /\
     (mk_ptr dst (vv_loc bvv)).ptr_location = LocMemory ==>
     !etv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (Subscript (EL k tys) obj idx)) = SOME etv ==>
       ?cw a len. eval_operand (vv_operand (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv)))) u = SOME cw /\
         a <= w2n cw /\ w2n cw + type_memory_size etv <= a + len /\
         a + len < dimword (:256) /\
         (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)) /\
    intcall_expr_cont fp ce env es sa s0 ee sb u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all intcall_tuple_add_landing >>
  disch_then (qspec_then `idx` strip_assume_tac) >>
  qexists_tac `u` >> conj_tac >- simp[] >>
  irule intcall_tuple_selected_post >> simp[] >>
  conj_tac >- gvs[] >>
  conj_tac >- fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  qexistsl_tac [`tv`, `vs`] >> gvs[vv_post_def]
QED
