(* The standalone nonword encoder's source conversion and capacities. *)
Theory bodyAbiEncodeStandaloneSourceMods
Ancestors
  bodyTypeBuiltinAbiMods bodyCopyReadPhysicalTypeMods exprBodyPreProps
  exprSimHypsDefs exprSimHyps exprSimWordArgs aggregateEvaluatedLayout
  abiEncodeArgsCase exprSimAbiEncodeArgsPhysicalCapacity abiEncodeEndpointMetadata
  abiBuiltinEncodeSource typedMemoryCopy logArgumentTypeEval vyperTypeEvalCaseProofs
  allocLimits compileEnv exprLowering vyperTypeABI vyperTypeSystem
  vyperInterpreter vyperContext vyperState vyperAST list arithmetic

Theorem nonword_source_operand_layout[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  ?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
    type_memory_bytes ce (expr_type e) = type_memory_size stv /\
    (~is_word_type (expr_type e) ==> type_memory_size stv < 2 ** 64)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  conj_asm1_tac >- (irule copy_lowered_fits_mods >> metis_tac[]) >>
  `env_consistent env cx es /\ sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_mods_def] >>
  simp[] >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all checked_expr_type_well_formed >>
  simp[well_formed_type_def,optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `stv` assume_tac) >>
  qexists_tac `stv` >> simp[] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size stv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> simp[] >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
  drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]
QED

Theorem nonword_source_result_type[local]:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode F mid) target [e]) es ==>
  ?limit. ann = BaseT (BytesT (Dynamic limit)) /\ target = TupleT [expr_type e] /\
    vyper_abi_size_bound (get_tenv cx) (expr_type e) + abi_encode_method_id_size mid <= limit
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, type_builtin_result_ok_def, abi_encode_size_ok_def] >>
  strip_tac >> gvs[]
QED

Theorem abi_encode_nonword_source_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode F mid) target [e]) es /\
  eval_exprs cx [e] (es with gas_obs := gs) = (INL [v],ee) /\
  ~is_word_type (lowered_value_type ce e) ==>
  ?tv av limit.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64 /\
    vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
      evaluate_type_builtin cx (AbiEncode F mid) target [expr_type e] [v] =
        INL (BytesV (abi_encode_method_id_bytes mid ++ bytes)) /\
      ann = BaseT (BytesT (Dynamic limit)) /\
      LENGTH bytes <= abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) /\
      LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= limit
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e es` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     drule type_builtin_body_arg_pre_mods >> simp[]) >>
  drule_then strip_assume_tac nonword_source_operand_layout >>
  `~is_word_type (expr_type e)` by (drule arg_type_fits_word_type >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    (drule (REWRITE_RULE [ETA_AX] eval_exprs_cons_cases) >>
     simp[evaluate_def,return_def] >> rpt strip_tac >> gvs[]) >>
  `?rt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
        value_has_type rt v /\ type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt` by
    (drule_all copy_read_physical_type_gas_obs_mods >> metis_tac[]) >>
  `type_memory_size rt < 2 ** 64` by
    (drule (cj 1 abi_args_fits_memory_bytes) >> disch_then (qspec_then `ce` mp_tac) >>
     fs[] >> decide_tac) >>
  drule_all_then strip_assume_tac (cj 1 vyper_to_abi_total) >>
  drule_then assume_tac (cj 1 abi_args_fits_abi_type) >>
  drule_all_then assume_tac (cj 1 abi_args_fits_conversion) >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by metis_tac[] >>
  drule_all_then assume_tac abi_args_physical_encoding_bound >>
  drule_then strip_assume_tac nonword_source_result_type >>
  qexistsl_tac [`rt`,`av`,`limit`] >> simp[] >>
  conj_tac >- (irule abi_builtin_encode_source_single >> simp[]) >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) =
   vyper_abi_size_bound (get_tenv cx) (expr_type e)` by
    metis_tac[abi_encode_evaluated_metadata] >>
  `abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) <=
   abi_size_bound ce.ce_struct_fields (expr_type e)` by
    (irule (cj 1 abi_args_fits_size_bound) >> simp[]) >>
  fs[abi_encode_method_id_size_def] >> decide_tac
QED
