(* Forget the conditional frame on the sequential ABI argument outcome. *)
Theory bodyFullAbiEncodeArgsCompose
Ancestors
  bodyFullAbiEncodePureFrame gasOutcomeFull

Theorem abi_encode_args_full_from_step:
  (!cx e tops ctx ce env es sa vv mid rest op sb shadow_sa shadow_mid shadow_sb
    shadow_ctx func shadow_func DF lo d s0 st0 G0 tn0 PG.
  body_expr_full_ok cx e /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce rest
   then compile_materialize_vv ce (lowered_value_type ce e) vv mid
   else unwrap_value ce vv mid) = (op,sb) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_mid) /\
  (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce rest
   then compile_materialize_vv ce (lowered_value_type ce e) vv shadow_mid
   else unwrap_value ce vv shadow_mid) = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state mid shadow_mid /\
  gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H rr ee G tn t. ?v tv.
      rr = INL v /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv v /\
      expr_post H ctx func ce cx e es sa sb s0 ee v op t /\
      expr_val_rel cx (lowered_value_type ce e) v op t /\
      expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op t /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_bytes ce (lowered_value_type ce e) < 2**64 /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      (~(~is_word_type (expr_type e) /\ exprs_can_mutate ce rest) ==>
        expr_store_bound cx (post_value_type ce e) v op t /\
        ptr_val_ok cx (post_value_type ce e) v op G tn t /\
        (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
        (~is_word_type (post_value_type ce e) ==> !w.
          eval_operand op t = SOME w ==>
          type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next)) /\
      (~is_word_type (expr_type e) /\ exprs_can_mutate ce rest ==>
        ?x w. op = Var x /\ lookup_var x t = SOME w /\
          FLOOKUP t.vs_allocas mid.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          FLOOKUP G x = SOME (w2n w,type_memory_size tv) /\
          ptr_buf_ok ce e op G t /\ lo <= w2n w /\
          ptr_covers G tn x t (type_memory_size tv) /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory tv v (w2n w) mem) /\
          w2n w + type_memory_size tv < dimword(:256) /\
          w2n w + type_memory_size tv <= t.vs_alloca_next /\
          (!name b sz. local_region ce es.scopes s0 name b sz ==>
            b+sz <= w2n w \/ w2n w+type_memory_size tv <= b)))
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r)) ==>
  !args cx tops ctx ce Inv env es sa ops sb shadow_sa shadow_sb shadow_ctx
    func shadow_func DF lo PG d st0 s0 G0 tn0.
  body_exprs_full_ok cx args /\ body_inv tops ctx ce cx /\ Inv es /\
  (!q. Inv q ==> expr_sim_inv ce cx env q) /\
  (!q gs. Inv q ==> Inv (q with gas_obs := gs)) /\
  EVERY (\e. !q. Inv q ==> expr_body_pre ce cx env e q) args /\
  EVERY (\e. !q v q'. Inv q /\
    bind (eval_expr cx e) (read_result cx) q = (INL v,q') ==>
    Inv q' /\ MAP FDOM q'.scopes = MAP FDOM q.scopes) args /\
  compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
  compile_abi_encode_args compile_expr ce (MAP gas_shadow_expr args) shadow_sa = (ops,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
    (\H rr ee G tn t. ?vs tvs.
      rr = INL vs /\ LENGTH tvs = LENGTH args /\
      abi_args_post H ctx func ce cx es sa sb s0 ee args ops vs t /\
      (!i. i < LENGTH args ==>
        evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
        value_has_type (EL i tvs) (EL i vs) /\
        type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs) /\
        type_memory_size (EL i tvs) < 2**64 /\
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) t /\
          op_taint tn (EL i ops) = {}) /\
        (~is_word_type (lowered_value_type ce (EL i args)) /\ 0 < type_memory_size (EL i tvs) ==>
          abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) t /\
          ?x w. EL i ops = Var x /\ lookup_var x t = SOME w /\
            ptr_covers G tn x t (type_memory_size (EL i tvs)) /\
            w2n w + type_memory_size (EL i tvs) < dimword(:256) /\
            w2n w + type_memory_size (EL i tvs) <= t.vs_alloca_next /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))) /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      EVERY (\op. !x. op = Var x ==> not_fresh_at sb x) ops /\
      Inv ee /\ MAP FDOM ee.scopes = MAP FDOM es.scopes)
    (\H rr ee gt r. wb_args_exit rr r /\ halt_exit H cx ee rr r)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  drule abi_encode_args_full_pure_frame_from_step >>
  disch_then drule_all >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[]
QED
