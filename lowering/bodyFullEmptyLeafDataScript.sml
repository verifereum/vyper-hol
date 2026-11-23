(* Named normal posts and the unchanged-state witness used by empty leaves. *)
Theory bodyFullEmptyLeafData
Ancestors
  bodySimFull exprSimFullBundleProps gasOutcomeFullCompose
  bodyPtrDefs loweringPosts exprSimMemDefs fragGasOriginPtr context vyperState

Definition expr_vv_sim_full_post_def:
  expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) =
    \H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func ce cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
      expr_sim_full_endpoint func sb s0 t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
           ~is_bytestring_type (post_value_type ce e) ==>
           vv_own ce cx (post_value_type ce e) sa sb ee tv vv t /\
           (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
               ptr_buf_ok ce e op G t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce e p.ptr_operand G t) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
End

Definition expr_vv_sim_full_hypotheses_def:
  expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) <=>
    compile_expr ce ty e sa = (vv,sb) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shb) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) /\
    local_ptrs_reserved ce sa /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
    return_buf_frame d ce sa s0 /\
    alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func ce cx es s0 /\
         storage_well_formed_on cx es (FST H) /\
         ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Theorem expr_vv_sim_full_via_bundle:
  expr_vv_sim_full (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es <=>
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_expr cx e) (es,s0,G0,tn0)
      (expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0))
      (\H res ee gt r.
        expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  simp[expr_vv_sim_full_def, expr_vv_sim_full_post_def, expr_sim_full_endpoint_def,
       expr_vv_sim_full_hypotheses_def, expr_sim_full_code_def,
       FUN_EQ_THM, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem gas_outcome_full_unchanged:
  !res. ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       Q H res (es with gas_obs := []) G tn s) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q R
Proof
  gen_tac >> strip_tac >> irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G`,`es`,`res`,`s`,`tn`] >> simp[gas_origin_ptr_path_rules]
QED
