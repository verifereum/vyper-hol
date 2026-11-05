(* Memory case of the body induction (bodyMemory's body_mem_mutual): type
   builtins, one leaf per builtin. *)
Theory bodyMemTypeBuiltin
Ancestors
  bodyMemoryPreds bodyMemTbBound bodyMemTbEmpty bodyMemTbConvert
  bodyMemTbExtract32 bodyMemTbAbiEncode bodyMemTbAbiDecode

Theorem body_type_builtin_mem_case:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt strip_tac >> Cases_on `tb`
  >~ [`TypeBuiltin _ Convert`]
  >- (irule body_type_builtin_convert_mem_case >> first_assum ACCEPT_TAC)
  >~ [`TypeBuiltin _ Extract32`]
  >- (irule body_type_builtin_extract32_mem_case >> first_assum ACCEPT_TAC)
  >~ [`TypeBuiltin _ (AbiEncode _ _)`]
  >- (irule body_type_builtin_abi_encode_mem_case >> first_assum ACCEPT_TAC)
  >~ [`TypeBuiltin _ (AbiDecode _)`]
  >- (irule body_type_builtin_abi_decode_mem_case >> first_assum ACCEPT_TAC) >>
  simp[body_type_builtin_bound_mem_case, body_type_builtin_empty_mem_case]
QED
