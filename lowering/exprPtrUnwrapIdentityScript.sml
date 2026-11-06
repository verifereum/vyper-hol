(* No-instruction forcing boundaries. *)
Theory exprPtrUnwrapIdentity
Ancestors
  bodyPtrDefs gasSummaryComposePtr exprSimUnwrap exprSimMemorySource
  exprLowering emitHelper compileEnv vyperState fragGasPathPtr gasSummary loweringPosts

Theorem unwrap_stack_marked_read_ptr:
  unwrap_value cenv (StackValue t op0) sm = (op, sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (StackValue t op0) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (StackValue t op0) ee G tn s /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op0 G s) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (expr_type e) v op Gf tnf u /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  simp[unwrap_value_def, comp_return_def] >> strip_tac >>
  gvs[ptr_vv_ok_def] >>
  qexistsl [`v`, `G`, `tn`, `s`] >> simp[] >>
  conj_tac
  >- (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
      conj_tac >- metis_tac[read_result_gas_obs] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, expr_post_def] >>
  first_assum ACCEPT_TAC
QED

Theorem unwrap_memory_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  ptr_buf_ok cenv e p.ptr_operand G s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (expr_type e) v op Gf tnf u /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def] >>
  qexistsl [`v`, `G`, `tn`, `s`] >> simp[] >>
  conj_tac
  >- (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
      conj_tac >- metis_tac[read_result_gas_obs] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, expr_post_def,
      ptr_val_ok_def] >>
  conj_tac
  >- (simp[expr_val_rel_def] >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  simp[expr_val_at_def] >> metis_tac[]
QED
