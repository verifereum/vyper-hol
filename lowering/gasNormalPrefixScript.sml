(* Concrete normal prefixes retain their source construct, compilation,
   full postcondition and exact cursor. No caller-selected post is used. *)
Theory gasNormalPrefix
Ancestors
  loweringPosts gasSummary allocaHistory exprLowering exprLoweringProps
  compileEnv venomState vyperInterpreter vyperState

Definition gas_value_prefix_def:
  gas_value_prefix memory (ctx, func, cenv, cx) (ty, e)
    (sa, sb, op) (es, s0) marks (v, ee, t) <=>
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx e) (read_result cx))
      (es, s0) marks (INL v) ee (OK t) /\
    expr_post ctx func cenv cx e es sa sb s0
      (ee with gas_obs := []) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (memory ==>
       alloca_history func s0 /\ alloca_history func t /\
       s0.vs_alloca_next <= t.vs_alloca_next)
End
