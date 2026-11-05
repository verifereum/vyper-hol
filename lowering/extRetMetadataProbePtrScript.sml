Theory extRetMetadataProbePtr
Ancestors
  retAbiPlanProps compileEnv exprLowering supportedTypes vyperTypeSystem
  vyperContext finite_map

Theorem supported_return_assignable_or_empty_struct:
  supported_return_type tops ret /\ ret <> NoneT /\
  well_formed_type (type_env tops) ret ==>
  assignable_type (type_env tops) ret \/
  (?id. ret = StructT id /\ supported_struct_fields tops id = SOME [])
Proof
  strip_tac >>
  Cases_on `?id. ret = StructT id /\ supported_struct_fields tops id = SOME []`
  >- simp[] >>
  disj1_tac >> irule supported_return_type_assignable >>
  simp[] >> metis_tac[]
QED

Theorem empty_struct_return_encoding:
  FLOOKUP cenv.ce_struct_fields (nsid_to_string id) = SOME [] ==>
  type_to_abi_enc_info cenv.ce_struct_fields cenv (StructT id) = AbiCopy 0
Proof
  strip_tac >>
  simp[Once type_to_abi_enc_info_def, is_abi_dynamic_def,
       type_memory_bytes_def, get_struct_fields_def]
QED
