(* Preserve the existing initialized allocation through the actual child run. *)
Theory bodyPtrMakeArrayChildOutcome
Ancestors
  bodyPtrPreds bodyPtrDefs bodyPtrMakeArrayPrefixFrame gasSummaryComposePtr
  exprSimProps loweringPosts

Theorem literal_child_outcome_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\
  compile_expr ce ty e sa = (vv,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ ptr_covers G0 tn0 root s0 capacity /\
  FLOOKUP s0.vs_allocas aid = SOME (addr,sz) /\ aid < sa.cs_next_id /\
  (!name b n. local_region ce es.scopes s0 name b n ==>
     addr+sz <= b \/ b+n <= addr) /\
  val_wf pt pv /\ val_footprint pt pv <= sz /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
     val_in_memory pt pv addr m) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx e) (es,s0,G0,tn0)
    (\res ee G tn s. ?raw. res = INL raw /\
      vv_post ctx func ce cx e es sa sb s0 ee raw vv s /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn s /\ ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
      (!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==>
        ptr_buf_ok ce e op G s) /\
      (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok ce e p.ptr_operand G s) /\
      ghost_kept ce es sa G0 tn0 s0 G tn /\ ptr_covers G tn root s capacity /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory pt pv addr m))
    (\res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_ptr d ctx PG func ce cx ty e es` by
    (qpat_x_assum `body_expr_ptr_ok _ _` mp_tac >>
     simp[Once body_expr_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  drule gas_outcome_ptr_conseq >> disch_then irule >> simp[] >>
  rpt strip_tac >> qexists `tv` >> simp[] >>
  conj_tac >- (irule child_old_pointer_coverage >> metis_tac[]) >>
  metis_tac[child_old_allocation_robust]
QED
