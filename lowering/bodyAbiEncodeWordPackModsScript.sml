(* Source value and buffer capacity for the direct singleton-word encoder. *)
Theory bodyAbiEncodeWordPackMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimAbiEncodePrefixWindow exprSimIfExpCompat
  entryDecodeProps vyperTypeABI vyperABI vyperTypeInvariants vyperTypeSystem
  vyperContext vyperAST compileEnv words

Theorem abi_encode_word_pack_source_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==>
  ?N av.
    ann = BaseT (BytesT (Dynamic N)) /\ ty = TupleT [expr_type e] /\
    well_typed_type_builtin_args (AbiEncode F mid) ty [expr_type e] /\
    vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
    enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av =
      word_to_bytes (typed_val_to_w256 tv v) T /\
    LENGTH (abi_encode_method_id_bytes mid ++
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <= N /\
    evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] =
      INL (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `env.type_defs = get_tenv cx /\
   sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_mods_def, env_consistent_def, env_context_consistent_def] >>
  qpat_assum `well_typed_expr _ (TypeBuiltin _ _ _ _)`
    (mp_tac o ONCE_REWRITE_RULE [well_typed_expr_def]) >>
  simp[type_builtin_result_ok_def,abi_encode_size_ok_def] >> strip_tac >> gvs[] >>
  `32 <= vyper_abi_size_bound (get_tenv cx) (expr_type e)` by
    (drule_all (exprSimIfExpCompatTheory.ifexp_compat_abi_size_bound_source) >>
     simp[abi_encode_word_size_bound]) >>
  `?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[cj 1 vyper_to_abi_total] >>
  drule_all_then strip_assume_tac vyper_to_abi_word_enc >>
  qexists_tac `av` >> simp[] >> conj_tac
  >- (simp[abi_encode_method_id_size_def] >>
      qpat_assum `abi_encode_method_id_size _ + _ <= _`
        (mp_tac o REWRITE_RULE [abi_encode_method_id_size_def]) >> decide_tac) >>
  simp[evaluate_type_builtin_def,needs_external_call_wrap_def,evaluate_abi_encode_bytes_def]
QED
