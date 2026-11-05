(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: slice. HELD: its S1 case (exprSimBuiltins' compile_slice_case,
   exprSimSlice on s1-builtins-aggregates) is still admitted. *)
Theory bodyMemBiSlice
Ancestors
  bodyMemoryPreds

Theorem body_builtin_slice_mem:
  !cx ty n es.
    (builtin_args_length_ok (Slice n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Slice n) es)
Proof
  cheat
QED
