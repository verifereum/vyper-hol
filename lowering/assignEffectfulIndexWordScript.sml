Theory assignEffectfulIndexWord
Ancestors
  assignEffectfulIndexPhysical stmtSimDefs exprSafeOperand exprOperandVar
  exprLowering context compileEnv

(* The execution boundary is intentionally conditional: the join supplies
   the physical unwrap run and its frame at the same endpoint. *)
Theorem assign_effectful_word_snapshot_path:
  is_word_type pty /\
  compile_snapshot_vv ce T (vv_with_type pty vv0) sm = (snap,sb) /\
  (!op sk. unwrap_value ce (vv_with_type pty vv0) sm = (op,sk) ==>
    ?u tv.
      evaluate_type (get_tenv cx) pty = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      gas_marked_path F ctx func s 0 (OK u) /\
      stmt_state_rel ctx func ce cx ee u /\
      eval_operand op u = SOME (typed_val_to_w256 tv v) /\
      safe_operand sk op /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      alloca_frame ce ee sm s ce ee u /\
      ~u.vs_halted /\ u.vs_current_bb = sk.cs_current_bb /\
      u.vs_inst_idx = LENGTH sk.cs_current_insts) ==>
  ?u tv w.
    evaluate_type (get_tenv cx) pty = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx ee u /\
    eval_operand (vv_operand snap) u = SOME w /\
    (!x. vv_operand snap = Var x ==> not_fresh_at sb x) /\
    (!lbl. vv_operand snap <> Label lbl) /\
    vv_location snap = NONE /\ w = typed_val_to_w256 tv v /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  `vv_type (vv_with_type pty vv0) = pty` by
    (Cases_on `vv0` >> simp[vv_with_type_def, vv_type_def]) >>
  strip_tac >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qexists_tac `u` >>
  gvs[vv_operand_def, vv_location_def, safe_operand_def]
QED
