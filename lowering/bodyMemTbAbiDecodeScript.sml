(* Memory case of the body induction for abi_decode (admitted; its own piece). *)
Theory bodyMemTbAbiDecode
Ancestors
  bodyMemoryPreds

Theorem body_type_builtin_abi_decode_mem_case:
  !cx v11 unwrap typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode unwrap) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (AbiDecode unwrap) typ es)
Proof
  cheat
QED
