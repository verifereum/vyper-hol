(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: keccak256 (S1: exprSimBuiltins' compile_keccak256_case,
   exprSimHash). *)
Theory bodyMemBiKeccak
Ancestors
  bodyMemoryPreds

Theorem body_builtin_keccak256_mem:
  !cx ty es.
    (builtin_args_length_ok Keccak256 (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty Keccak256 es)
Proof
  cheat
QED
