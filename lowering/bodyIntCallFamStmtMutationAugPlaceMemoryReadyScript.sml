(* Memory read readiness and counted readonly loads for AugAssign. *)
Theory bodyIntCallFamStmtMutationAugPlaceMemoryReady
Ancestors
  bodyIntCallFamStmtMutationLoad stmtSimAugAssignPlaceMemory
  bodySimAugPlaceLive bodyIntCallJointContract loweringPosts
  bodyAugPlaceTarget bodySim exprSimHypsDefs
  emitHelperProps venomInst venomState

Theorem intcall_aug_place_memory_read_ready:
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_stmt fp.jc_tops bindings (AugAssign ty tg bop rhs) /\
  ((?bt fld. tg = AttributeTarget bt fld) \/
   (?bt key. tg = SubscriptTarget bt key)) /\
  type_stmt env ret_ty (AugAssign ty tg bop rhs) = SOME env' /\
  expr_body_pre ce fp.jc_cx env rhs es /\
  target_indices_pre ce fp.jc_cx env tg /\
  eval_target_place fp.jc_cx tg es = (INL (MemoryPlace id path),ee) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee
    (PlaceR (MemoryPlace id path)) (Type ty) rp u /\
  intcall_expr_cont fp ce env es sa s ee sb u ==>
  ?cur tv w.
    read_place fp.jc_cx (MemoryPlace id path) ee = (INL cur,ee) /\
    place_type_value fp.jc_cx (MemoryPlace id path) ee = (INL tv,ee) /\
    evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv cur /\
    type_bits ty MOD 8 = 0 /\ eval_operand (FST rp) u = SOME w /\
    mload (w2n w) u = typed_val_to_w256 tv cur /\
    expr_body_pre ce fp.jc_cx env rhs ee
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ expr_sim_inv ce fp.jc_cx env ee` by
    fs[expr_body_pre_def,intcall_expr_cont_def,intcall_expr_res_def] >>
  `?info. supported_target_info fp.jc_tops bindings tg = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  `?cur. read_place fp.jc_cx (MemoryPlace id path) ee = (INL cur,ee)` by
    fs[target_post_def,place_readable_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
   ?w. eval_operand (FST rp) u = SOME w /\
     place_ptr_rel ce fp.jc_cx u (PlaceR (MemoryPlace id path)) w
       (FST (SND rp)) (Type ty)` by fs[target_post_def] >>
  `?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
     place_type_value fp.jc_cx (MemoryPlace id path) ee = (INL tv,ee)` by
    metis_tac[aug_place_memory_type_read] >>
  gvs[] >> drule_at (Pos (el 5)) aug_place_memory_access_ready >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env rhs ee` by
    metis_tac[aug_place_rhs_pre_target] >>
  gvs[]
QED

Theorem intcall_aug_place_memory_load_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_op MLOAD [dst] sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  eval_operand dst s = SOME w /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    eval_operand op u = SOME (mload (w2n w) s) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >> irule intcall_emit_readonly_cont >>
  simp[is_terminator_def] >> qexistsl [`[dst]`,`MLOAD`] >> simp[is_terminator_def] >>
  gen_tac >> drule step_MLOAD >> simp[]
QED
