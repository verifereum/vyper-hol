Theory exprSimAbiEncodeTupleZero
Ancestors
  exprSimAbiEncodeTranslatedZero exprSimAbiEncodeEmptySource exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodeSourceMetadata abiTupleEncodeMemory retAbiPlanProps
  exprLowering compileEnv list

Theorem abi_encode_tuple_zero_descriptor:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\ LENGTH values = LENGTH args /\
  abi_tuple_bytes ce (ZIP (values,MAP expr_type args)) = 0 ==>
  type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)) = AbiCopy 0 \/
  type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)) = AbiComplex []
Proof
  strip_tac >>
  `type_memory_bytes ce (TupleT (MAP expr_type args)) = 0` by
    (gvs[abi_tuple_encode_bytes_zip]) >>
  `!k. k < LENGTH args ==> type_memory_bytes ce (expr_type (EL k args)) = 0` by
    (qpat_x_assum `type_memory_bytes ce (TupleT _) = 0` mp_tac >>
     simp[type_memory_bytes_def, SUM_eq_0, MEM_MAP, MEM_EL] >> metis_tac[]) >>
  `!k. k < LENGTH args ==> ~is_abi_dynamic ce.ce_struct_fields (expr_type (EL k args))` by
    (gen_tac >> strip_tac >>
     drule_all abi_encode_body_args_indexed_types >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     drule_all abi_encode_body_evaluated_metadata >> strip_tac >>
     `type_memory_size tv = 0` by metis_tac[] >>
     drule_all abi_encode_zero_size_static >> strip_tac >>
     drule (cj 1 vyper_to_abi_type_dynamic) >> metis_tac[]) >>
  `~is_abi_dynamic ce.ce_struct_fields (TupleT (MAP expr_type args))` by
    (simp[is_abi_dynamic_def, EXISTS_MEM, MEM_MAP, MEM_EL] >> metis_tac[]) >>
  simp[type_to_abi_enc_info_def]
QED
