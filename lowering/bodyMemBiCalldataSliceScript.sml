(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: msg.data slices (S1: exprSimCalldataSlice's
   compile_calldata_slice_call_case). *)
Theory bodyMemBiCalldataSlice
Ancestors
  bodyMemoryPreds

Theorem body_builtin_calldata_slice_mem:
  !cx ty n es.
    (builtin_args_length_ok (CalldataSlice n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (CalldataSlice n) es)
Proof
  cheat
QED
