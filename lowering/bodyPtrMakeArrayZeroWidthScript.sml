(* Zero-sized slots still evaluate their child and destination ADD.  Only
   their equal-layout store is empty; no source/destination access is made. *)
Theory bodyPtrMakeArrayZeroWidth
Ancestors
  bodyPtrMakeArrayConsInvariant bodyPtrMakeArrayAdd context compileEnv
  vyperValue valueEncoding exprLowering bodyPtrMakeArrayEmission
  bodyPtrMakeArrayAddFrame venomState venomExecSemantics ptrDiscipline
  bodyPtrMakeArrayNonwordUnwrap freshWrites emitHelperProps fragGasPath
  vyperEvalExprPreservesScopesDom exprLoweringProps wordArgsPtr
  fragGasPathPtr loweringPosts exprSimMemoryTransport

Theorem literal_zero_store_identity:
  ~is_word_type ty /\ ~is_bytestring_type ty /\ type_memory_bytes ce ty = 0 ==>
  compile_store_memory ce src dst ty ty sa = ((),sa)
Proof
  simp[compile_store_memory_def, compile_copy_memory_def, comp_return_def]
QED

Theorem literal_empty_tuple_layout:
  evaluate_type tenv (TupleT []) = SOME (TupleTV []) /\
  type_memory_bytes ce (TupleT []) = 0 /\
  type_memory_size (TupleTV []) = 0 /\
  compile_store_memory ce src dst (TupleT []) (TupleT []) sa = ((),sa)
Proof
  simp[evaluate_type_def, type_slot_size_def, type_memory_bytes_def,
       type_memory_size_def, compile_store_memory_def, is_word_type_def,
       is_bytestring_type_def, compile_copy_memory_def, comp_return_def]
QED

(* No destination coverage is requested: off may be exactly capacity, and
   the allocation itself may have capacity zero.  ADD is still executed. *)
Theorem literal_zero_child_add:
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
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
    ptr_vv_ok cx (expr_type e) raw vv es' H tm z /\
    (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
    tm.t_mem = tn.t_mem /\ ghost_inv d ce cx es' H tm z /\
    ghost_kept ce esi si G0 tn0 s0 H tm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all emit_op_fetch_boundary >> strip_tac >> fs[] >>
  qexistsl [`(update_var out (a+n2w off) s) with vs_inst_idx := SUC s.vs_inst_idx`,
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
  conj_tac >- simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  conj_tac >- (irule emit_binop_ghost_inv >> metis_tac[]) >>
  irule emit_binop_ghost_kept >> metis_tac[]
QED

Theorem literal_zero_child_materialize:
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value ce vv sn = (op,sb) /\
  compile_store_memory ce op (Var out) (expr_type e) (lowered_value_type ce e) sb = ((),sc) /\
  type_memory_bytes ce (expr_type e) = 0 /\
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ stmt_state_rel ctx func ce cx esi s0 /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ ~ce.ce_is_ctor /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
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
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    expr_post ctx func ce cx e esi si sc s0 es' v op z /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce esi si G0 tn0 s0 H tm /\
    stmt_state_rel ctx func ce cx es' z /\ ~z.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sc = sb` by
    (gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def]) >>
  gvs[] >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all literal_zero_child_add >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `~z.vs_halted` by metis_tac[gas_path_ptr_erase, gas_path_normal] >>
  `stmt_state_rel ctx func ce cx es' z` by gvs[vv_post_def] >>
  drule literal_nonword_unwrap >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `si.cs_next_id <= sn.cs_next_id /\ si.cs_next_var <= sn.cs_next_var` by
    (drule emitted_insts_emit_op >> strip_tac >>
     mp_tac (cj 1 compile_expr_ci_mono) >>
     disch_then (qspecl_then [`ce`, `expr_type e`, `e`, `si`] mp_tac) >>
     simp[ci_mono_def] >> decide_tac) >>
  `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  `wb_frame ce esi es' si s0 z` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ sn _ _ _ _ _` mp_tac >>
     simp[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `ghost_kept ce esi si G0 tn0 s0 H' tm'` by
    (irule (Q.INST [`es1` |-> `es'`, `s1` |-> `z`, `sb` |-> `sn`, `G1` |-> `H`,
                    `tn1` |-> `tm`] wordArgsPtrTheory.ghost_kept_wb_trans) >>
     simp[] >> metis_tac[]) >>
  qexistsl [`z'`, `H'`, `tm'`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED

Theorem literal_zero_cell:
  val_wf tv v /\ val_footprint tv v = 0 /\ val_in_memory tv v a mem ==>
  literal_prefix_ok [(tv,v,p,0)] tn s
Proof
  simp[literal_prefix_cell] >> rpt strip_tac >>
  irule val_in_memory_relocate_footprint >> simp[] >>
  qexistsl [`mem`, `a`] >> simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

(* The actual expr_post and ghost_kept returned above are precisely the
   materialization interface. No equality between independent runs is used. *)
Theorem literal_zero_frame_extend:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\
  stmt_state_rel ctx func ce cx ees sf /\
  local_ptrs_reserved ce fr /\ local_ptrs_reserved ce si /\
  expr_post ctx func ce cx e esi si sb s0 es' v op z /\
  ghost_kept ce esi si G0 tn0 s0 H tm /\ ghost_inv d ce cx es' H tm z /\
  eval_expr cx e esi = (res,es') /\
  si.cs_next_var <= sb.cs_next_var /\ si.cs_next_id <= sb.cs_next_id /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  val_wf tv v /\ val_footprint tv v = 0 /\ val_in_memory tv v a mem ==>
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es' sb H tm z (cells ++ [(tv,v,addr+off,0)]) off /\
  literal_prefix_ok (cells ++ [(tv,v,addr+off,0)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_loop_frame_materialized >> strip_tac >>
  conj_tac
  >- (`off <= capacity` by metis_tac[literal_loop_frame_allocation] >>
      drule literal_loop_frame_advance >>
      disch_then (qspecl_then [`v`, `tv`, `0`] mp_tac) >> simp[]) >>
  simp[] >> irule literal_zero_cell >> metis_tac[]
QED
