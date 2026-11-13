(* Pointer-safe sequencing around the code-array suffix. *)
Theory bodyPtrSubscriptSeamArrayCodeCompose
Ancestors
  bodyPtrSubscriptMarkedCompose bodyPtrDefs gasSummaryComposePtr
  exprSimSubscriptArraySource exprSimDefs exprSimProps
  vyperState exprLowering compileEnv vyperStorageTrace gasSummary fragGasMode

Theorem code_array_after_base_ptr:
  ~subscript_reads_base cx obj idx ==>
  gas_marked_exec F (ctx,func) (eval_expr cx obj) (es,s0) left
    (INL captured) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_path_ptr (cx_dead H cx) 0 ctx func PG G0 tn0 s0 (LENGTH left)
         G1 tn1 (OK t)) /\
  expr_sim_ptr d ctx PG func cenv cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sm = (iop,si) /\
  fn_has_code sm si func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := []) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
       storage_well_formed_on cx (mid with gas_obs := []) (FST H) /\
       ghost_inv H d cenv cx (mid with gas_obs := []) G1 tn1 t) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v Gi tni u.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx idx) (read_result cx))
       (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
     (!H. valid_horizon cx st0 H raw.storage_trace ==>
          gas_path_ptr (cx_dead H cx) 0 ctx func PG G1 tn1 t (LENGTH imarks)
            Gi tni (OK u) /\
          expr_post H ctx func cenv cx idx (mid with gas_obs := []) sm si t
            (raw with gas_obs := []) v iop u /\
          u.vs_current_bb = si.cs_current_bb /\
          u.vs_inst_idx = LENGTH si.cs_current_insts /\
          ghost_inv H d cenv cx (raw with gas_obs := []) Gi tni u /\
          ptr_val_ok cx (post_value_type cenv idx) v iop Gi tni u /\
          (~is_word_type (post_value_type cenv idx) ==>
           ptr_buf_ok cenv idx iop Gi u) /\
          ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gi tni) ==>
     gas_summary_ptr_at (\H. cx_dead H cx) (ctx,func) PG cx st0 []
       (select_result cx (expr_type obj) captured (ValueSubscript v))
       (raw with gas_obs := [],u,Gi,tni) Q
       (\H res ee gt out. expr_exit res out)) ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
    (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0)
    Q (\H res ee gt out. expr_exit res out)
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`si`,`iop`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` array_index_outcome_compose_ptr))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  simp[storage_trace_frame_select, storage_trace_frame_read_result,
       evaluate_storage_trace_frame, storage_trace_frame_bind_all] >>
  qexistsl [`G1`, `\H v ee Gi tni u.
    expr_post H ctx func cenv cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    u.vs_current_bb = si.cs_current_bb /\ u.vs_inst_idx = LENGTH si.cs_current_insts /\
    ghost_inv H d cenv cx ee Gi tni u /\
    ptr_val_ok cx (post_value_type cenv idx) v iop Gi tni u /\
    (~is_word_type (post_value_type cenv idx) ==> ptr_buf_ok cenv idx iop Gi u) /\
    ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gi tni`, `tn1`] >> simp[] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
