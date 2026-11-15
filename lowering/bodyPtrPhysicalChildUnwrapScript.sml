(* Materialization preserves the child's physical post-value semantics. *)
Theory bodyPtrPhysicalChildUnwrap
Ancestors
  bodyPtrMakeArrayChildUnwrap bodyPtrMakeArrayExternalCaller
  bodyPtrMakeArrayNonwordUnwrap bodyPtrMakeArrayExternalUnwrap
  exprPtrUnwrapMarked exprSimHyps
  bodyPtrDefs loweringPosts exprLowering context compileEnv
  fragGasPathPtr fragGasPath exprSimHypsDefs valueCopyBytes typedMemoryCopy
  bodyPtrMakeArrayEmission bodyPtrMakeArrayAdd bodyPtrMakeArrayAddFrame
  bodyPtrMakeArrayAddCoverage emitHelperProps venomState venomExecSemantics
  ptrDiscipline wordArgsPtr vyperEvalExprPreservesScopesDom exprLoweringProps
  loweringStateRelDefs bodyPtrSubscriptSeamTupleLayoutBridge

Theorem unwrap_stack_physical_ptr_path:
  unwrap_value ce (StackValue t op) sm = (result,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (StackValue t op) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type ce e) raw (StackValue t op) ee G tn s /\
  ~s.vs_halted ==>
  sb = sm /\ result = op /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK s) /\
  expr_post ctx func ce cx e es sa sb s0 ee v result s /\
  ptr_val_ok cx (post_value_type ce e) v result G tn s
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  simp[cj 1 gas_path_ptr_rules, expr_post_def] >> metis_tac[]
QED

Theorem unwrap_memory_physical_ptr_path:
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  unwrap_value ce (LocatedValue t p) sm = (result,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue t p) ee G tn s /\
  ~s.vs_halted ==>
  sb = sm /\ result = p.ptr_operand /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK s) /\
  expr_post ctx func ce cx e es sa sb s0 ee v result s /\
  ptr_val_ok cx (post_value_type ce e) v result G tn s
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  simp[cj 1 gas_path_ptr_rules, expr_post_def, ptr_val_ok_def,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
      metis_tac[]) >>
  strip_tac >> gvs[] >>
  imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[] >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> metis_tac[]
QED

Theorem literal_nonword_unwrap_physical:
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value ce vv sn = (op,sb) /\ fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func ce cx e esi si sn s0 es' raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv es' G tn s /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  ghost_inv d ce cx es' G tn s /\ stmt_state_rel ctx func ce cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~ce.ce_is_ctor /\ ~is_word_type (expr_type e) ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (post_value_type ce e) v op H tm z /\ ptr_buf_ok ce e op H z /\
    (~is_bytestring_type (expr_type e) ==>
      ptr_mem_ok cx (lowered_value_type ce e) v op H tm z) /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce es' sn G tn s H tm /\
    stmt_state_rel ctx func ce cx es' z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\
    (!x n. not_fresh_at sn x /\ ptr_covers G tn x s n ==>
      ptr_covers H tm x z n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (post_value_type ce e)` by
    (`type_widens_to env.type_defs (post_value_type ce e) (expr_type e)` by
       (metis_tac[expr_body_pre_def, post_value_type_widens]) >>
     metis_tac[return_source_word_widens_eq]) >>
  `!z H tm. ptr_val_ok cx (post_value_type ce e) v op H tm z ==>
     (~is_bytestring_type (expr_type e) ==>
       ptr_mem_ok cx (lowered_value_type ce e) v op H tm z)` by
    metis_tac[aggregate_lowered_post_type, ptr_val_ok_def] >>
  Cases_on `vv`
  >- (drule_all unwrap_stack_physical_ptr_path >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
      qexistsl [`s`, `G`, `tn`] >> simp[ghost_kept_def]) >>
  rename1 `LocatedValue t p` >>
  `~is_word_type t` by
    (drule vv_post_located_type >> strip_tac >> gvs[] >>
     imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule_all unwrap_memory_physical_ptr_path >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
      qexistsl [`s`, `G`, `tn`] >> simp[ghost_kept_def]) >>
  `post_value_type ce e = expr_type e` by
    (drule_all external_located_post_type >> simp[]) >>
  gvs[] >> drule_all external_nonword_unwrap >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >> qexistsl [`z`, `H`, `tm`] >> simp[] >>
  (conj_tac >- metis_tac[gas_path_ptr_erase, gas_path_normal] >>
   rpt strip_tac >>
   drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`) unwrapped_old_pointer_coverage >>
   disch_then (qspecl_then [`z`, `x`, `n`] mp_tac) >> simp[])
QED

(* ADD preserves source pointer semantics independently of its type. *)
Theorem literal_child_add_typed_endpoint:
  !base cap.
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (base,cap) /\
  base + cap <= dimword(:256) /\ off < capacity /\ off+n <= capacity /\
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
    z.vs_current_bb = sn.cs_current_bb /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func ce cx e esi si sn s0 es' raw vv z /\
    ptr_vv_ok cx physical raw vv es' H tm z /\
    (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
    tm.t_mem = tn.t_mem /\
    ghost_inv d ce cx es' H tm z /\
    ghost_kept ce esi si G0 tn0 s0 H tm /\
    ptr_covers H tm out z n /\ lookup_var out z = SOME (a+n2w off)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all emit_op_fetch_boundary >> strip_tac >> fs[] >>
  qexistsl [`(update_var out (a+n2w off) s) with
               vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst sm.cs_next_id ADD
       [Var root; Lit (n2w off)] [out]) (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst sm.cs_next_id ADD
       [Var root; Lit (n2w off)] [out]) s (update_var out (a+n2w off) s) tn`] >>
  conj_tac
  >- (irule emit_clean_binop_ptr_path >>
      simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[] >>
  conj_tac >- (irule emit_binop_vv_post >> metis_tac[]) >>
  conj_tac >- (irule binop_source_ptr_vv_ok >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule binop_source_ptr_buf_ok >>
      simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule binop_source_ptr_buf_ok >>
      simp[] >> gvs[vv_operand_def] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  conj_tac >- (irule emit_binop_ghost_inv >> metis_tac[]) >>
  conj_tac >- (irule emit_binop_ghost_kept >> metis_tac[]) >>
  reverse conj_tac >- simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  drule add_destination_coverage >> simp[arithmeticTheory.ADD_COMM] >>
  disch_then (qspecl_then [`off`, `n`, `PG`, `sm.cs_next_id`, `out`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem literal_child_add_unwrap_physical:
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_all literal_child_add_typed_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `~z.vs_halted` by metis_tac[gas_path_ptr_erase, gas_path_normal] >>
  `stmt_state_rel ctx func ce cx es' z` by gvs[vv_post_def] >>
  `not_fresh_at sn out` by
    (drule emitted_insts_emit_op >> simp[not_fresh_at_def] >> metis_tac[]) >>
  drule_all literal_nonword_unwrap_physical >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept ce esi si G0 tn0 s0 H' tm'` by
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
  qexistsl [`z'`, `H'`, `tm'`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED
