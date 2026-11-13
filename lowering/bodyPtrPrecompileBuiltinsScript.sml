(*
 * Precompile builtins: ecrecover, ecadd, ecmul.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   precompile_builtin_expr_ptr_ok
 *)
Theory bodyPtrPrecompileBuiltins
Ancestors
  bodyPtrPrecompileBuiltinsECAddRunner bodyPtrPrecompileBuiltinsECMulRunner
  bodyPtrPrecompileBuiltinsRecoveryRunner
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem precompile_builtin_expr_ptr_ok:
  !cx ty bt es.
    (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  (conj_asm2_tac >- metis_tac[expr_sim_ptr_of_vv] >>
   (irule recovery_expr_vv_sim_ptr ORELSE irule ecadd_expr_vv_sim_ptr ORELSE
    irule ecmul_expr_vv_sim_ptr) >>
   metis_tac[])
QED
