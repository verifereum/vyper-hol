(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: concat. HELD: its S1 case (exprSimBuiltins'
   compile_concat_case, exprSimConcat on s1-builtins-aggregates) is still
   admitted. *)
Theory bodyMemBiConcat
Ancestors
  bodyMemoryPreds

Theorem body_builtin_concat_mem:
  !cx ty n es.
    (builtin_args_length_ok (Concat n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Concat n) es)
Proof
  cheat
QED
