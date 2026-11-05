Theory stmtSimLogArgsRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogArgs stmtSimLogArgsGrowth exprReasonOperand exprOperandVar
  exprSimWordArgs supportedTypes  exprSimOps
  loweringSlice exprLoweringProps freshWrites fragExec emitHelperProps varsExt compileEnv
  vyperInterpreter vyperState vyperTyping
  vyperEvalExprPreservesScopesDom

Theorem log_scalar_base[local]:
  supported_scalar_type ty ==> ?bt. ty = BaseT bt
Proof
  cheat
QED

Theorem compile_log_eval_all_nil_sim:
  frag_exec ctx sa sa (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. log_args_post ctx func cenv cx es sa sa s0 es [] [] s)
    (wb_args_exit (INL []))
Proof
  cheat
QED

Theorem log_args_frag_at_entry[local]:
  (!s. P s ==> s = s0) /\
  ((~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
    frag_exec ctx sa sb P Q R) ==>
  frag_exec ctx sa sb P Q R
Proof
  cheat
QED

Theorem compile_log_eval_all_safe_sim:
  !args ctx func cenv cx R es sa xs sb rr es' s0 env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    (case rr of INL vs => T | INR exc => expr_res_ok (INR exc : value + exception)) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\
        log_args_post ctx func cenv cx es sa sb s0 es' xs vs s /\
        EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                   (!lab. FST p <> Label lab)) xs)
      (wb_args_exit rr)
Proof
  cheat
QED




Theorem compile_log_eval_all_sim:
  !args ctx func cenv cx R es sa xs sb rr es' s0 env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    (case rr of INL vs => T | INR exc => expr_res_ok (INR exc : value + exception)) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\
        log_args_post ctx func cenv cx es sa sb s0 es' xs vs s)
      (wb_args_exit rr)
Proof
  cheat
QED
