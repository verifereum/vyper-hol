(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: ecrecover (S1: exprSimPrecompiles'
   compile_ecrecover_call_case). *)
Theory bodyMemBiECRecover
Ancestors
  bodyMemoryPreds

Theorem body_builtin_ecrecover_mem:
  !cx ty es.
    (builtin_args_length_ok ECRecover (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty ECRecover es)
Proof
  cheat
QED
