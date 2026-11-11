(* Memory case of the body induction for abi_encode (admitted; its own piece). *)
Theory bodyMemTbAbiEncode
Ancestors
  bodyMemoryPreds abiEncodeContinuationMemory

Theorem body_type_builtin_abi_encode_mem_case:
  !cx v11 ensure mid typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (AbiEncode ensure mid) typ es)
Proof
  cheat
QED
