(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: blobhash (S1: exprSimBuiltins' compile_blobhash_case). *)
Theory bodyMemBiBlobHash
Ancestors
  bodyMemoryPreds

Theorem body_builtin_blobhash_mem:
  !cx ty es.
    (builtin_args_length_ok BlobHash (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty BlobHash es)
Proof
  cheat
QED
