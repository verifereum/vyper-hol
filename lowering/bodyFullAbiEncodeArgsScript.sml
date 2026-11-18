(* ABI arguments share one physical endpoint across all horizons. *)
Theory bodyFullAbiEncodeArgs
Ancestors
  bodyFullAbiEncodeArgStep bodyFullAbiEncodeArgsCompose
  bodyFullPreds abiEncodeArgsSim abiEncodeArgsCase gasOutcomeFullCompose
  gasShadowCompile gasShadowCompileHelpers gasShadowState gasShadowCompileConvert
  exprLoweringProps exprLowering compileEnv
  gasOutcomeFull fragGasOriginPtr fragExec bodySimFull bodyPtrDefs loweringPosts
  exprSimHyps exprSimSource exprSimWordArgs venomState venomExecSemantics vyperInterpreter
  vyperStorageTrace vyperStorageFootprint vyperStorageBackend vyperState list arithmetic words

Theorem abi_encode_args_full:
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
  match_mp_tac abi_encode_args_full_from_step >>
  rpt gen_tac >> MATCH_ACCEPT_TAC abi_encode_arg_step_full
QED
