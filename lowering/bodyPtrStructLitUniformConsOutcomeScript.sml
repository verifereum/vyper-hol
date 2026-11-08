(* Counted child evaluation followed by uniform forcing and field storage. *)
Theory bodyPtrStructLitUniformConsOutcome
Ancestors bodyPtrStructLitUniformMarkedCons bodyPtrMakeArrayConsOutcome
  bodyPtrMakeArrayConsBind bodyPtrMakeArrayConsInvariant gasSummaryComposePtr
  bodyPtrDefs loweringPosts

Theorem structlit_uniform_cons_outcome_ptr:
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  k = type_memory_bytes ce (expr_type e) /\ off+k <= capacity /\
  post_value_type ce e = expr_type e ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_cons_compiler_stages >> strip_tac >>
  drule literal_loop_frame_runtime >> strip_tac >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  irule literal_result_bind_outcome_ptr >>
  qexists `\raw ee H tm z.
    vv_post ctx func ce cx e es si sm s0 ee raw vv z /\
    z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d ce cx ee H tm z /\ ptr_vv_ok cx (expr_type e) raw vv ee H tm z /\
    (!tag arg. vv = StackValue tag arg /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok ce e arg H z) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    ghost_kept ce es si G0 tn0 s0 H tm` >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> fs[] >>
      `off+k <= capacity` by decide_tac >>
      drule_all structlit_uniform_marked_cons_outcome >> simp[]) >>
  drule gas_outcome_ptr_conseq >> disch_then irule >>
  simp[] >> rpt strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >> metis_tac[]
QED
