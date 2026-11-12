Theory bodyPtrSubscriptSeamArrayMemoryFinish
Ancestors
  bodyPtrSubscriptSeamArrayMemoryAfterIndex bodyPtrSubscriptMarkedCompose
  bodyPtrSubscriptSeamArrayMemoryPrepare bodyPtrDefs gasSummaryComposePtr
  exprSimSubscriptArraySource exprSimSubscriptArrayFramed exprSimProps
  exprLoweringProps exprSimHypsDefs gasContext gasOutcome gasSummary
  exprSimDefs vyperState list

Theorem fixed_array_after_base_ptr:
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_expr cx obj)
    (es,s0,G0,tn0) left (INL captured) mid Gb tnb (OK u) /\
  expr_sim_ptr d ctx PG func cenv cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sb = (iop,sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sb /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok (mid with gas_obs := []) /\
  stmt_state_rel ctx func cenv cx (mid with gas_obs := []) u /\
  ghost_inv d cenv cx (mid with gas_obs := []) Gb tnb u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!imarks raw iv Gi tni q.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (bind (eval_expr cx idx) (read_result cx))
      (mid with gas_obs := [],u,Gb,tnb) imarks (INL iv) raw Gi tni (OK q) /\
    expr_post ctx func cenv cx idx (mid with gas_obs := []) sb sc u (raw with gas_obs := []) iv iop q /\
    q.vs_current_bb = sc.cs_current_bb /\ q.vs_inst_idx = LENGTH sc.cs_current_insts /\
    ghost_inv d cenv cx (raw with gas_obs := []) Gi tni q /\
    ptr_val_ok cx (post_value_type cenv idx) iv iop Gi tni q /\
    (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx iop Gi q) /\
    ghost_kept cenv (mid with gas_obs := []) sb Gb tnb u Gi tni ==>
    gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
      (select_result cx (expr_type obj) captured (ValueSubscript iv))
      (raw with gas_obs := [],q,Gi,tni) Q (\res ee gt out. expr_exit res out)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0)
    Q (\res ee gt out. expr_exit res out)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sb`,`sc`,`iop`,`u`,`Gb`,`tnb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!res out. (?exc. res = (INR exc : value + exception) /\
      expr_exit (INR exc : eval_result + exception) out) = expr_exit res out` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `!res out. _` (fn th => once_rewrite_tac[GSYM th]) >>
  disch_tac >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  irule (BETA_RULE (Q.ISPEC
    `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` array_index_outcome_post_compose_ptr))) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED
