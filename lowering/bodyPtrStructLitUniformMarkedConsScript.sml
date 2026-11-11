(* Normal marked child continuation, retaining the literal's original frame. *)
Theory bodyPtrStructLitUniformMarkedCons
Ancestors bodyPtrStructLitUniformEndpoint bodyPtrMakeArrayConsSource
  bodyPtrMakeArrayConsOutcome bodyPtrMakeArrayConsBind gasSummaryComposePtr
  fragGasPathPtr fragGasPath loweringPosts bodyPtrDefs exprSimHypsDefs
  bodyPtrMakeArrayConsInvariant

Theorem structlit_uniform_marked_cons_outcome:
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
  post_value_type ce e = expr_type e /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_expr cx e)
    (es,s0,G0,tn0) marks (INL raw) ee G tn (OK t) /\ ee.gas_obs = [] /\
  vv_post ctx func ce cx e es si sm s0 ee raw vv t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d ce cx ee G tn t /\ ptr_vv_ok cx (expr_type e) raw vv ee G tn t /\
  (!tag arg. vv = StackValue tag arg /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok ce e arg G t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G t) /\
  ghost_kept ce es si G0 tn0 s0 G tn ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (read_result cx raw) (ee,t,G,tn)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule literal_marked_child_materialises >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_expr cx e marked = _` >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
     ees fr sf Gf tnf marked si G0 tn0 s0 cells off` by
    (gvs[Abbr `marked`, literal_loop_frame_def, ghost_inv_def, ghost_kept_def,
       exprSimWordArgsTheory.wb_frame_gas_obs] >> metis_tac[]) >>
  `ghost_kept ce marked si G0 tn0 s0 G tn` by
    (gvs[Abbr `marked`, ghost_kept_def] >> metis_tac[]) >>
  `expr_body_pre ce cx env e marked` by simp[Abbr `marked`] >>
  `lookup_var root t = SOME (n2w addr)` by
    (gvs[literal_loop_frame_def, vv_post_def] >> metis_tac[]) >>
  `ptr_covers G tn root t capacity /\ FLOOKUP G root = SOME (addr,capacity)` by
    (gvs[literal_loop_frame_def, ghost_kept_def, ptr_covers_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >>
     metis_tac[gas_path_ptr_erase, gas_path_normal]) >>
  drule_at (Pat `eval_expr _ _ _ = _`) structlit_uniform_cons_endpoint >>
  disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL v`, `ee`, `H`, `tm`, `OK z`] >> gvs[]
QED
