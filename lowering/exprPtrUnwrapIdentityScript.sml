(* No-instruction forcing boundaries. *)
Theory exprPtrUnwrapIdentity
Ancestors
  bodyPtrDefs gasSummaryComposePtr exprSimUnwrap exprSimUnwrapProps exprSimMemorySource valueCopyBytes
  exprLowering emitHelper compileEnv vyperState fragGasPathPtr gasSummary loweringPosts

(* The family forms: the endpoint is chosen once, before the horizons; the
   path holds under every dead mask and the posts at every horizon in P. *)
Theorem unwrap_stack_marked_read_ptr_horizons:
  unwrap_value cenv (StackValue t op0) sm = (op, sb) /\
  (!H. P H ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv (StackValue t op0) s /\
     ghost_inv H d cenv cx ee G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv (StackValue t op0) ee G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op0 G s) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    (!D. gas_marked_exec_ptr D (ctx,func) PG (read_result cx tv)
           (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u)) /\
    (!H. P H ==>
       expr_post H ctx func cenv cx e es sa sb s0 ee v op u /\
       ghost_inv H d cenv cx ee Gf tnf u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_val_ok cx (post_value_type cenv e) v op Gf tnf u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  simp[unwrap_value_def, comp_return_def] >> strip_tac >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
  qexistsl [`v`, `G`, `tn`, `s`] >> rpt conj_tac
  >- (gen_tac >> simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
      conj_tac >- metis_tac[read_result_gas_obs] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[])
  >- (gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def, expr_post_def] >>
      first_assum ACCEPT_TAC) >>
  gvs[]
QED

Theorem unwrap_stack_marked_read_ptr:
  unwrap_value cenv (StackValue t op0) sm = (op, sb) /\
  vv_post H ctx func cenv cx e es sa sm s0 ee tv (StackValue t op0) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv H d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv (StackValue t op0) ee G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op0 G s) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead H cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post H ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv H d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (post_value_type cenv e) v op Gf tnf u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  qspec_then `\H'. H' = H` mp_tac (Q.GEN `P` unwrap_stack_marked_read_ptr_horizons) >>
  impl_tac >- simp[] >>
  simp[] >> strip_tac >>
  qexistsl [`v`, `Gf`, `tnf`, `u`] >> simp[]
QED

Theorem unwrap_memory_marked_read_ptr_horizons:
  unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  (!H. P H ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
     ghost_inv H d cenv cx ee G tn s) /\ P H0 /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ptr_buf_ok cenv e p.ptr_operand G s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    (!D. gas_marked_exec_ptr D (ctx,func) PG (read_result cx tv)
           (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u)) /\
    (!H. P H ==>
       expr_post H ctx func cenv cx e es sa sb s0 ee v op u /\
       ghost_inv H d cenv cx ee Gf tnf u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_val_ok cx (post_value_type cenv e) v op Gf tnf u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `vv_post H0 ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s` by
    metis_tac[] >>
  `~is_word_type (post_value_type cenv e)` by
    (qpat_x_assum `!H. P H ==> _` kall_tac >> strip_tac >>
     fs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_vv_ok_def] >> strip_tac >>
  qexistsl [`v`, `G`, `tn`, `s`] >> simp[ptr_val_ok_def] >> conj_tac
  >- (gen_tac >> simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
      conj_tac >- metis_tac[read_result_gas_obs] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  irule expr_post_of_vv_post_memory >> simp[] >> qexists `t` >>
  simp[] >> metis_tac[vv_post_read_result]
QED

Theorem unwrap_memory_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv H d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ptr_buf_ok cenv e p.ptr_operand G s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?v Gf tnf u.
    gas_marked_exec_ptr (cx_dead H cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee Gf tnf (OK u) /\
    expr_post H ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv H d cenv cx ee Gf tnf u /\
    ptr_val_ok cx (post_value_type cenv e) v op Gf tnf u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gf u) /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  qspecl_then [`\H'. H' = H`, `H`] mp_tac
    (Q.GENL [`P`, `H0`] unwrap_memory_marked_read_ptr_horizons) >>
  impl_tac >- simp[] >>
  simp[] >> strip_tac >>
  qexistsl [`v`, `Gf`, `tnf`, `u`] >> simp[]
QED
