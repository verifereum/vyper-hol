(* Invoke the RHS induction hypothesis with its common joint endpoint and
   retain the concrete and ghost frames needed by any AugAssign target. *)
Theory augAssignFullRhs
Ancestors
  bodyFullPreds bodySimFull bodyPtrDefs gasOutcomeFull
  loweringPosts stmtSimProps exprSimDefs exprSimProps exprSimHypsDefs exprLoweringProps
  gasShadow vyperInterpreter vyperState

Theorem augassign_rhs_invoke_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==>
       ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. ?ex. res = INR ex /\
       !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by
    (qpat_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ty`, `es`]
       mp_tac) >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >> disch_then drule_all >> disch_tac >>
  irule gas_outcome_full_post_mono >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED
