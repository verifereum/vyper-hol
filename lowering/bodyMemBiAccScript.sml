(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: account members such as x.balance (S1: exprSimBuiltins'
   compile_acc_case; a bare x.code is rejected by the allocation check, as
   exprSimAccCode on s1-builtins-aggregates shows). *)
Theory bodyMemBiAcc
Ancestors
  bodyMemoryPreds

Theorem body_builtin_acc_mem:
  !cx ty item es.
    (builtin_args_length_ok (Acc item) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Acc item) es)
Proof
  cheat
QED
