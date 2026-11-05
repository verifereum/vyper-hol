(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: method_id (S1: exprSimBuiltins' compile_method_id_case). *)
Theory bodyMemBiMethodId
Ancestors
  bodyMemoryPreds

Theorem body_builtin_method_id_mem:
  !cx ty es.
    (builtin_args_length_ok MethodId (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty MethodId es)
Proof
  cheat
QED
