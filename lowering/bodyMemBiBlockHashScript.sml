(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: blockhash (S1: exprSimBuiltins' compile_blockhash_case). *)
Theory bodyMemBiBlockHash
Ancestors
  bodyMemoryPreds

Theorem body_builtin_blockhash_mem:
  !cx ty es.
    (builtin_args_length_ok BlockHash (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty BlockHash es)
Proof
  cheat
QED
