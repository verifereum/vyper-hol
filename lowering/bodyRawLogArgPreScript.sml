(*
 * RawLog's arguments inherit the call's body precondition.
 *
 * TOP-LEVEL:
 *   expr_body_pre_raw_log_arg
 *)
Theory bodyRawLogArgPre
Ancestors
  exprSimSource exprSimHypsDefs supportedExprTraverse allocLimits
  vyperTypeCallGraph vyperTypeSystem vyperAST list

Theorem expr_body_pre_raw_log_arg:
  !cenv cx env ann args dflt e es es'.
    expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def,
     vyperTypeCallGraphTheory.int_calls_expr_def,
     byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED
