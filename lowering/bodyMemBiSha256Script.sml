(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: sha256 (S1: exprSimBuiltins' compile_sha256_case, exprSimHash). *)
Theory bodyMemBiSha256
Ancestors
  bodyMemoryPreds

Theorem body_builtin_sha256_mem:
  !cx ty es.
    (builtin_args_length_ok Sha256 (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty Sha256 es)
Proof
  cheat
QED
