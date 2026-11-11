Theory exprSimAbiEncodeTupleResult
Ancestors
  exprSimAbiEncodeTupleCounted exprSimAbiEncodeNonwordResult
  exprSimAbiEncodeBytesOwnership exprSimAbiEncodeStagedObserver exprSimAbiEncodeStagedFrame
  exprBopSimProps exprSimProps freshWrites loweringPosts
  abiBuiltinEncodeSource abiBuiltinEncodeMethod abiBuiltinEncodeRun
  valueEncoding valueEncodingProps vyperInterpreter abiBuiltinEncodeCode vyperAST
  exprSimAbiEncodeTupleResources exprSimHypsDefs vyperTypeSystem compileEnv
  abiEncoderCounters words list abiBuiltinEncodeContext vyperState


Theorem abi_encode_tuple_result_memory:
  well_typed_type_builtin_args (AbiEncode ensure mid0) target tys /\
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

Theorem abi_encode_tuple_observation_vv_post:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
  enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
  expr_type (TypeBuiltin ann (AbiEncode ensure mid0) target args) = BaseT (BytesT (Dynamic N)) /\
  LENGTH (abi_encode_method_id_bytes mid0 ++ enc ct rv) <= N /\
  lower_abi_encode ensure mid src ei
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged = (out,final) /\
  fn_has_code staged final func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce staged /\
  abi_encode_staged_observation ctx func ce cx es' staged out mid
    (32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))+
      (case mid of NONE => 0 | SOME _ => 4))) p ct rv s actual /\
  wb_frame ce es origin s0 s /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= staged.cs_next_var /\ origin.cs_next_id <= staged.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode ensure mid0) target args)
    es origin final s0 es' (Value (BytesV (abi_encode_method_id_bytes mid0 ++ enc ct rv)))
    (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode ensure mid0) target args))
      <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_staged_origin_frame >> strip_tac >>
  drule_all abi_encode_args_numerical_capacity >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `well_typed_type_builtin_args (AbiEncode ensure mid0) target (MAP expr_type args)` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  qpat_assum `abi_encode_staged_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encode_staged_observation_def] >> strip_tac >>
  drule_all abi_encode_tuple_result_memory >> disch_then (qspec_then `N` assume_tac) >>
  `!name b n. local_region ce es'.scopes actual name b n ==>
    p+(32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))+
      (case mid of NONE => 0 | SOME _ => 4))) <= b \/ b+n <= p` by
    (drule lower_abi_encode_trace >> strip_tac >>
     drule_all abi_builtin_encode_code >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     irule abi_encode_setup_row_local_exclusion >>
     qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
     qpat_assum `stmt_state_rel ctx func ce cx es' actual` (irule_at Any) >>
     metis_tac[]) >>
  drule abi_encode_strict_id_growth >> strip_tac >>
  irule abi_encode_bytes_vv_post >> goal_assum (drule_at Any) >>
  simp[read_result_def, return_def] >>
  qexistsl [`staged.cs_next_id`, `p`,
    `32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))+
      (case mid of NONE => 0 | SOME _ => 4))`] >>
  `p < dimword (:256)` by decide_tac >>
  simp[] >> Cases_on `mid0` >>
  gvs[abi_encode_method_id_bytes_def, well_typed_type_builtin_args_def] >> metis_tac[]
QED
