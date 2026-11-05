(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: len (S1: exprSimBuiltins' compile_len_case, exprSimLen). *)
Theory bodyMemBiLen
Ancestors
  bodyMemoryPreds

Theorem body_builtin_len_mem:
  !cx ty es.
    (builtin_args_length_ok Len (LENGTH es) ==> body_expr_mem_ok cx (HD es)) ==>
    body_expr_mem_ok cx (Builtin ty Len es)
Proof
  cheat
QED
