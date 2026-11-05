(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: ceil (S1: exprSimBuiltins' compile_ceil_case). *)
Theory bodyMemBiCeil
Ancestors
  bodyMemoryPreds

Theorem body_builtin_ceil_mem:
  !cx ty es.
    (builtin_args_length_ok Ceil (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty Ceil es)
Proof
  cheat
QED
