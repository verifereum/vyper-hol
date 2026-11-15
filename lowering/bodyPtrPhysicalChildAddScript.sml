(* Physical child values survive an endpoint-safe literal slot address. *)
Theory bodyPtrPhysicalChildAdd
Ancestors
  bodyPtrPhysicalChildUnwrap bodyPtrMakeArrayAdd bodyPtrMakeArrayAddFrame
  bodyPtrMakeArrayEmission venomInst fragGasPathPtr fragGasPath
  assignBasePtrOffset typedCopyPtr emitHelperProps context compileEnv
  loweringStateRelDefs loweringPosts venomState venomExecSemantics
  bodyPtrDefs ptrDiscipline finite_map wordArgsPtr
  freshWrites exprLoweringProps vyperEvalExprPreservesScopesDom

Theorem literal_physical_child_add_endpoint:
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ off+n <= capacity /\
  w2n a + off < dimword(:256) /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx physical raw vv es' G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sn.cs_current_bb /\ z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func ce cx e esi si sn s0 es' raw vv z /\
    ptr_vv_ok cx physical raw vv es' H tm z /\
    (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
    tm.t_mem = tn.t_mem /\ ghost_inv d ce cx es' H tm z /\
    ghost_kept ce esi si G0 tn0 s0 H tm /\
    ptr_covers H tm out z n /\ lookup_var out z = SOME (a+n2w off)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all emit_op_fetch_boundary >> strip_tac >> fs[] >>
  qexistsl_tac [`(update_var out (a+n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sm.cs_next_id ADD [Var root; Lit (n2w off)] [out])
       (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst sm.cs_next_id ADD [Var root; Lit (n2w off)] [out]) s
       (update_var out (a+n2w off) s) tn`] >>
  conj_tac
  >- (irule emit_clean_binop_ptr_path >>
      simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >> conj_tac >- simp[] >>
  conj_tac >- (irule emit_binop_vv_post >> metis_tac[]) >>
  conj_tac >- (irule binop_source_ptr_vv_ok >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule binop_source_ptr_buf_ok >>
      simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule binop_source_ptr_buf_ok >>
      simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >> conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[copy_len_binop_ghost_frame] >>
  conj_tac >- (irule emit_binop_ghost_inv >> metis_tac[]) >>
  conj_tac >- (irule emit_binop_ghost_kept >> metis_tac[]) >>
  reverse conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `off < dimword(:256)` by decide_tac >>
  gvs[ptr_covers_def] >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame,
    step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE, wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
    arithmeticTheory.LESS_MOD] >> decide_tac
QED
Theorem literal_physical_child_add_unwrap:
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
  ptr_covers G tn root s capacity /\ off+n <= capacity /\
  w2n a + off < dimword(:256) /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn /\
  fn_inst_ids_distinct func /\ ~ce.ce_is_ctor /\ ~is_word_type (expr_type e) ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (post_value_type ce e) v op H tm z /\ ptr_buf_ok ce e op H z /\
    (~is_bytestring_type (expr_type e) ==>
      ptr_mem_ok cx (lowered_value_type ce e) v op H tm z) /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce esi si G0 tn0 s0 H tm /\
    stmt_state_rel ctx func ce cx es' z /\ ~z.vs_halted /\
    ptr_covers H tm out z n /\ lookup_var out z = SOME (a+n2w off)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_all literal_physical_child_add_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `~z.vs_halted` by metis_tac[gas_path_ptr_erase, gas_path_normal] >>
  `stmt_state_rel ctx func ce cx es' z` by gvs[vv_post_def] >>
  `not_fresh_at sn out` by
    (drule emitted_insts_emit_op >> simp[not_fresh_at_def] >> metis_tac[]) >>
  drule_all literal_nonword_unwrap_physical >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `z2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `ghost_kept ce esi si G0 tn0 s0 G2 tn2` by
    (`si.cs_next_id <= sn.cs_next_id /\ si.cs_next_var <= sn.cs_next_var` by
       (drule emitted_insts_emit_op >> strip_tac >>
        mp_tac (cj 1 compile_expr_ci_mono) >>
        disch_then (qspecl_then [`ce`, `expr_type e`, `e`, `si`] mp_tac) >>
        simp[ci_mono_def] >> decide_tac) >>
     `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
       metis_tac[eval_expr_preserves_scopes_dom] >>
     `wb_frame ce esi es' si s0 z` by
       (qpat_x_assum `vv_post _ _ _ _ _ _ _ sn _ _ _ _ _` mp_tac >>
        simp[vv_post_def, wb_frame_def] >> metis_tac[]) >>
     irule (Q.INST [`es1` |-> `es'`, `s1` |-> `z`, `sb` |-> `sn`, `G1` |-> `H`,
                    `tn1` |-> `tm`] wordArgsPtrTheory.ghost_kept_wb_trans) >>
     simp[] >> metis_tac[]) >>
  qexistsl [`z2`, `G2`, `tn2`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED
