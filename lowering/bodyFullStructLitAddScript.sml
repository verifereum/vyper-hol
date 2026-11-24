(* The destination ADD runs between the child expression and its unwrap. *)
Theory bodyFullStructLitAdd
Ancestors
  bodyFullStructLitAddEndpoint

Theorem structlit_child_add_full:
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (region_base,cap) /\
  w2n a + off < dimword(:256) /\ off + n <= capacity /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sm.cs_next_var /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es si sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_kept_at lo ce es si Gi ti s0 G tn /\
  alloca_history func s /\ alloca_inv s ==>
  ?t G' tn'.
    (!D lo' explicit. allocas_from lo' s ==>
      gas_origin_ptr_path (D,lo',explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func ce cx e es si sm s0 ee tv vv t /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' t) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G' tn' t /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G' t) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G' t) /\
    ghost_kept_at lo ce es si Gi ti s0 G' tn' /\
    alloca_history func t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    ptr_covers G' tn' out t n /\ lookup_var out t = SOME (a+n2w off)
Proof
  strip_tac >> drule_all structlit_child_add_full_endpoint >>
  disch_then (qspec_then `PG`
    (qx_choose_then `t` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_rewrite_tac[]
QED
