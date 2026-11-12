(* Pointer-safe sequencing around the code-array suffix. *)
Theory bodyPtrSubscriptSeamArrayCodeCompose
Ancestors
  bodyPtrSubscriptMarkedCompose bodyPtrDefs gasSummaryComposePtr
  exprSimSubscriptArraySource exprSimDefs exprSimProps
  vyperState exprLowering compileEnv

Theorem code_array_after_base_ptr:
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_expr cx obj)
    (es,s0,G0,tn0) left (INL captured) mid G1 tn1 (OK t) /\
  expr_sim_ptr d ctx PG func cenv cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sm = (iop,si) /\
  fn_has_code sm si func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := []) /\
  stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
  ghost_inv d cenv cx (mid with gas_obs := []) G1 tn1 t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v Gi tni u.
     gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
       (bind (eval_expr cx idx) (read_result cx))
       (mid with gas_obs := [],t,G1,tn1) imarks (INL v) raw Gi tni (OK u) /\
     expr_post ctx func cenv cx idx (mid with gas_obs := []) sm si t
       (raw with gas_obs := []) v iop u /\
     u.vs_current_bb = si.cs_current_bb /\ u.vs_inst_idx = LENGTH si.cs_current_insts /\
     ghost_inv d cenv cx (raw with gas_obs := []) Gi tni u /\
     ptr_val_ok cx (post_value_type cenv idx) v iop Gi tni u /\
     (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx iop Gi u) /\
     ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gi tni ==>
     gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
       (select_result cx (expr_type obj) captured (ValueSubscript v))
       (raw with gas_obs := [],u,Gi,tni) Q (\res ee gt out. expr_exit res out)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0)
    Q (\res ee gt out. expr_exit res out)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sm`,`si`,`iop`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` array_index_outcome_compose_ptr))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qexists `\v ee Gi tni u.
    expr_post ctx func cenv cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    u.vs_current_bb = si.cs_current_bb /\ u.vs_inst_idx = LENGTH si.cs_current_insts /\
    ghost_inv d cenv cx ee Gi tni u /\
    ptr_val_ok cx (post_value_type cenv idx) v iop Gi tni u /\
    (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx iop Gi u) /\
    ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gi tni` >> simp[] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
