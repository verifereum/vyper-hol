(* One endpoint for nonword identity and external materialization branches.
   esi is the actual, possibly gas-marked, child evaluation input. *)
Theory bodyPtrMakeArrayNonwordUnwrap
Ancestors
  bodyPtrMakeArrayExternalUnwrap bodyPtrMakeArrayUnwrapIdentity
  bodyPtrMakeArrayLayoutTransport exprPtrUnwrapMarked exprSimProps
  bodyPtrDefs loweringPosts exprLowering context compileEnv bodyPtrMakeArrayMemoryFrame
  fragGasPathPtr fragGasPath exprSimHyps valueCopyBytes

Theorem unwrapped_old_pointer_coverage:
  ghost_kept ce es' sn G tn s H tm /\
  (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s) /\
  not_fresh_at sn root /\ ptr_covers G tn root s n ==>
  ptr_covers H tm root z n
Proof
  gvs[ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem literal_nonword_unwrap:
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value ce vv sn = (op,sb) /\ fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func ce cx e esi si sn s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  ghost_inv d ce cx es' G tn s /\ stmt_state_rel ctx func ce cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~ce.ce_is_ctor /\ ~is_word_type (expr_type e) /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (expr_type e) v op H tm z /\ ptr_buf_ok ce e op H z /\
    ptr_mem_ok cx (lowered_value_type ce e) v op H tm z /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce es' sn G tn s H tm /\
    stmt_state_rel ctx func ce cx es' z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\
    (!x n. not_fresh_at sn x /\ ptr_covers G tn x s n ==>
      ptr_covers H tm x z n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce e = expr_type e` by
    (qpat_assum `int_calls_expr e = [] \/ _` strip_assume_tac
     >- (irule exprSimHypsTheory.post_value_type_no_calls >>
         first_assum ACCEPT_TAC) >>
     irule post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  `!s H tm. ptr_val_ok cx (expr_type e) v op H tm s ==>
    ptr_mem_ok cx (lowered_value_type ce e) v op H tm s` by
    (rpt strip_tac >> irule make_array_child_ptr_mem_lowered >>
     simp[] >> reverse conj_tac >- gvs[ptr_val_ok_def] >>
     qexistsl [`env`, `esi`, `es'`] >>
     simp[vyperStateTheory.bind_def]) >>
  Cases_on `vv`
  >- (drule_all unwrap_stack_ptr_path >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
      qexistsl [`s`, `G`, `tn`] >> simp[ghost_kept_def]) >>
  rename1 `LocatedValue t p` >>
  `~is_word_type t` by
    (drule vv_post_located_type >> strip_tac >> gvs[] >>
     imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule_all unwrap_memory_ptr_path >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
      qexistsl [`s`, `G`, `tn`] >> simp[ghost_kept_def]) >>
  `t = expr_type e` by (drule vv_post_located_type >> gvs[]) >>
  drule_all external_nonword_unwrap >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >> qexistsl [`z`, `H`, `tm`] >> simp[] >>
  (conj_tac >- metis_tac[gas_path_ptr_erase, gas_path_normal] >>
   rpt strip_tac >>
   drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`) unwrapped_old_pointer_coverage >>
   disch_then (qspecl_then [`z`, `x`, `n`] mp_tac) >> simp[])
QED

Theorem unwrapped_old_allocation_robust:
  vv_post ctx func ce cx e esi si sn s0 es' raw vv s /\
  expr_post ctx func ce cx e esi si sb s0 es' v op z /\
  ghost_kept ce es' sn G tn s H tm /\
  FLOOKUP s0.vs_allocas aid = SOME (addr,sz) /\ aid < si.cs_next_id /\
  aid < sn.cs_next_id /\
  (!name p k. local_region ce esi.scopes s0 name p k ==>
    addr+sz <= p \/ p+k <= addr) /\
  (!name p k. local_region ce es'.scopes s name p k ==>
    addr+sz <= p \/ p+k <= addr) /\
  val_wf ty value /\ val_footprint ty value <= sz /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory ty value addr m) ==>
  !m. mem_agree_outside tm.t_mem z.vs_memory m ==>
    val_in_memory ty value addr m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP s.vs_allocas aid = SOME (addr,sz) /\
   mem_bytes_at addr sz z.vs_memory = mem_bytes_at addr sz s.vs_memory` by
    (gvs[vv_post_def, expr_post_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >> irule bodyPtrMakeArrayMemoryFrameTheory.robust_val_in_memory_shrinking_frame >>
  simp[] >> qexistsl [`tn.t_mem`, `tm.t_mem`, `s.vs_memory`, `z.vs_memory`, `sz`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_def] >> metis_tac[]
QED
