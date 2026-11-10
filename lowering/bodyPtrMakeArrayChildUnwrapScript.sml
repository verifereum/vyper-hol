(* Execute destination arithmetic and materialization on the same child path. *)
Theory bodyPtrMakeArrayChildUnwrap
Ancestors
  bodyPtrMakeArrayChildAdd bodyPtrMakeArrayNonwordUnwrap
  emitHelperProps fragGasPathPtr fragGasPath loweringPosts compileEnv loweringStateRelDefs
  wordArgsPtr vyperEvalExprPreservesScopesDom exprLoweringProps

Theorem literal_child_add_unwrap:
  !base cap.
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value ce vv sn = (op,sb) /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ stmt_state_rel ctx func ce cx esi s0 /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (base,cap) /\
  base + cap <= dimword(:256) /\ off < capacity /\ off+n <= capacity /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn /\
  fn_inst_ids_distinct func /\ ~ce.ce_is_ctor /\ ~is_word_type (expr_type e) /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (expr_type e) v op H tm z /\ ptr_buf_ok ce e op H z /\
    ptr_mem_ok cx (lowered_value_type ce e) v op H tm z /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce esi si G0 tn0 s0 H tm /\
    stmt_state_rel ctx func ce cx es' z /\ ~z.vs_halted /\
    ptr_covers H tm out z n /\ lookup_var out z = SOME (a+n2w off)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op G s` by metis_tac[] >>
  drule_all literal_child_add_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `~z.vs_halted` by metis_tac[gas_path_ptr_erase, gas_path_normal] >>
  `stmt_state_rel ctx func ce cx es' z` by gvs[vv_post_def] >>
  `not_fresh_at sn out` by
    (drule emitted_insts_emit_op >> simp[not_fresh_at_def] >> metis_tac[]) >>
  `!t op. vv = StackValue t op ==> ptr_buf_ok ce e op H z` by metis_tac[] >>
  drule_all literal_nonword_unwrap >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept ce esi si G0 tn0 s0 H' tm'` by
    (`si.cs_next_id <= sn.cs_next_id /\ si.cs_next_var <= sn.cs_next_var` by
       (drule emitted_insts_emit_op >> strip_tac >>
        mp_tac (cj 1 compile_expr_ci_mono) >>
        disch_then (qspecl_then [`ce`, `expr_type e`, `e`, `si`] mp_tac) >>
        simp[ci_mono_def] >> decide_tac) >>
     `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
       metis_tac[eval_expr_preserves_scopes_dom] >>
     `wb_frame ce esi si s0 z` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ sn _ _ _ _ _` mp_tac >>
        simp[vv_post_def, wb_frame_def] >> metis_tac[]) >>
     irule ghost_kept_wb_trans >> simp[] >> conj_tac >- metis_tac[] >>
     qexistsl [`H`, `es'`, `z`, `sn`, `tm`] >> simp[]) >>
  qexistsl [`z'`, `H'`, `tm'`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED
