Theory exprSimAbiEncodeNonwordResult
Ancestors
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeCapacity
  abiBuiltinEncodeSource vyperTypeInvariants vyperTypeSystem vyperAST exprSimHypsDefs
  exprSimAbiEncodeSourceMetadata abiBuiltinEncodeMethod valueEncoding
  valueEncodingProps abiBuiltinEncodeRun

Theorem abi_encode_nonword_result_type:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es ==>
  ?N. expr_type (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
        BaseT (BytesT (Dynamic N)) /\
      ty = TupleT [expr_type e] /\
      vyper_abi_size_bound (get_tenv cx) (expr_type e) +
        abi_encode_method_id_size mid <= N
Proof
  simp[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
    abi_encode_size_ok_def, expr_type_def] >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[]
QED

Theorem abi_encode_nonword_result_bound:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  ?N. expr_type (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
        BaseT (BytesT (Dynamic N)) /\
      ty = TupleT [expr_type e] /\
      LENGTH (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <= N
Proof
  strip_tac >> drule_all abi_encode_nonword_length_bound >> strip_tac >>
  drule abi_encode_nonword_result_type >> strip_tac >>
  drule_all abi_encode_body_evaluated_metadata >> strip_tac >>
  qexists_tac `N` >> simp[abi_encode_method_id_size_def] >>
  gvs[abi_encode_method_id_size_def] >> decide_tac
QED

Theorem abi_encode_nonword_result_memory:
  well_typed_type_builtin_args (AbiEncode F mid0) ty [ety] /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  mload p actual = n2w (LENGTH bytes + (case mid of NONE => 0 | SOME _ => 4)) /\
  mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4))
    (LENGTH bytes) actual.vs_memory = bytes /\
  (case mid of NONE => T | SOME selector =>
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) ==>
  val_in_memory (BaseTV (BytesT (Dynamic N)))
    (BytesV (abi_encode_method_id_bytes mid0 ++ bytes)) p actual.vs_memory
Proof
  strip_tac >> drule abi_builtin_encode_checked_prefix >> strip_tac >>
  Cases_on `mid`
  >- (Cases_on `mid0` >> gvs[abi_builtin_encode_prefix_def,
        abi_encode_method_id_bytes_def, val_in_memory_def, mem_word_at_eq_mload]) >>
  fs[] >> drule_all abi_builtin_encode_method_value >> strip_tac >>
  Cases_on `mid0` >> gvs[abi_builtin_encode_prefix_def,
    abi_encode_method_id_bytes_def, val_in_memory_def, mem_word_at_eq_mload,
    abi_builtin_encode_method_bytes_length]
QED
