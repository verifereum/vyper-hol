(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: uint2str (S1: exprSimBuiltins' compile_uint2str_case). Waits
   for the trunk's buffer-size change to compile_uint2str_def. *)
Theory bodyMemBiUint2Str
Ancestors
  bodyMemoryPreds bodyMemBiUint2StrPost

Theorem body_builtin_uint2str_mem:
  !cx ty n es.
    (builtin_args_length_ok (Uint2Str n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Uint2Str n) es)
Proof
  cheat
QED
