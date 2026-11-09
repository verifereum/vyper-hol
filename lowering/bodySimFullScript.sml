(* Source GAS origins, memory bounds and pointer ghosts share one witness. *)
Theory bodySimFull
Ancestors
  gasOutcomeFull bodyPtrDefs exprSimMemDefs stmtSimDefs
  gasShadow gasShadowState gasShadowUnit gasExplicitSites
  exprLowering stmtLowering loweringPosts compileEnv allocaHistory
  vyperInterpreter vyperState venomState venomWf list option

Definition expr_sim_full_def:
  expr_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !sa sb shadow_sa shadow_sb op s0 G0 tn0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa =
        (op, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) (bind (eval_expr cx e) (read_result cx))
        (es, s0, G0, tn0)
        (\res ee G tn t. ?v. res = INL v /\
          expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (expr_type e) v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at D lo d cenv cx ee G tn t /\
          ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
          (~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

Definition expr_vv_sim_full_def:
  expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      compile_expr cenv ty (gas_shadow_expr e) shadow_sa = (vv, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) (eval_expr cx e) (es, s0, G0, tn0)
        (\res ee G tn t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
            ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at D lo d cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
          (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                   ptr_buf_ok cenv e op G t) /\
          (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

(* Both compilations include local declarations and return the same
   environment, as stmt_env and stmts_env do. *)
Definition stmt_frag_full_def:
  stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (m : compile_env compiler) (shadow_m : compile_env compiler)
    source es <=>
    !sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'.
      m sa = (cenv', sb) /\
      shadow_m shadow_sa = (cenv', shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      return_buf_frame d cenv sa s0 /\
      stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) source (es, s0, G0, tn0)
        (\res ee G tn t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel ctx func cenv'' cx ee t /\
          return_buf_frame d cenv'' sb t /\ alloca_history func t /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at D lo d cenv'' cx ee G tn t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP G x = FLOOKUP G0 x /\
               op_taint tn (Var x) = op_taint tn0 (Var x)))
        (\res ee gt r.
          !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
End

Definition frame_ret_ok_full_def:
  frame_ret_ok_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es /\
              expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es) ==>
      stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo))
        (stmt_env cenv' lctx ret_ty (Return (OPTION_MAP gas_shadow_expr eo)))
        (eval_stmt cx (Return eo)) es
End
