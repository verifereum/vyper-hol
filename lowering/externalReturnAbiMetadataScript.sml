(* Source environments and actual external-return ABI metadata. *)
Theory externalReturnAbiMetadata
Ancestors
  exprLowering compileEnv abiEncoderProps abiEncoderSourceProducer
  externalReturnZeroLayout externalRawReturnType retAbiPlanProps
  typedNormalizeProducer supportedProgram supportedTypes
  e2eDefs vyperContext vyperInterpreter vyperTypeSystem vyperTyping

Theorem source_deployment_return_tenv:
  source_deployment_rel tops am tx ==>
  get_tenv (initial_evaluation_context am.sources am.layouts tx NONE) =
    type_env tops
Proof
  simp[source_deployment_rel_def, get_tenv_def,
       initial_evaluation_context_def, type_env_all_modules_def,
       type_env_def, finite_mapTheory.FUNION_FEMPTY_2]
QED

(* Positive outer size does not exclude an empty nested struct. *)
Theorem positive_nested_return_not_assignable[local]:
  supported_place_type [StructDecl "Empty" []]
    (TupleT [BaseT (UintT 256); StructT (NONE,"Empty")]) /\
  evaluate_type (type_env [StructDecl "Empty" []])
    (TupleT [BaseT (UintT 256); StructT (NONE,"Empty")]) =
    SOME (TupleTV [BaseTV (UintT 256); StructTV []]) /\
  0 < type_memory_size (TupleTV [BaseTV (UintT 256); StructTV []]) /\
  ~assignable_type (type_env [StructDecl "Empty" []])
    (TupleT [BaseT (UintT 256); StructT (NONE,"Empty")])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

(* Concrete compiler outputs with the actual empty-struct field table. *)
Theorem nested_empty_metadata_probe[local]:
  !c. c.ce_struct_fields = FEMPTY |+ ("Empty", []) ==>
    type_to_abi_enc_info c.ce_struct_fields c
      (TupleT [BaseT (UintT 256); StructT (NONE,"Empty")]) = AbiCopy 32 /\
    type_to_abi_enc_info c.ce_struct_fields c
      (TupleT [BaseT (BytesT (Dynamic 8)); StructT (NONE,"Empty")]) =
      AbiComplex [(AbiBytestring 8,32,64,T); (AbiCopy 0,0,0,F)] /\
    type_to_abi_enc_info c.ce_struct_fields c
      (ArrayT (StructT (NONE,"Empty")) (Dynamic 3)) =
      AbiDynArray (AbiCopy 0) 0 0 F /\
    type_memory_size (TupleTV [BaseTV (UintT 256); StructTV []]) = 32 /\
    type_memory_size (TupleTV [BaseTV (BytesT (Dynamic 8)); StructTV []]) = 64 /\
    type_memory_size (ArrayTV (StructTV []) (Dynamic 3)) = 32
Proof
  rpt strip_tac >>
  simp[type_to_abi_enc_info_def, type_memory_bytes_def] >>
  EVAL_TAC
QED

Theorem nested_empty_plan_probe[local]:
  abi_enc_plan (type_env [StructDecl "Empty" []])
    (TupleT [BaseT (UintT 256); StructT (NONE,"Empty")]) (AbiCopy 32) /\
  abi_enc_plan (type_env [StructDecl "Empty" []])
    (TupleT [BaseT (BytesT (Dynamic 8)); StructT (NONE,"Empty")])
    (AbiComplex [(AbiBytestring 8,32,64,T); (AbiCopy 0,0,0,F)]) /\
  abi_enc_plan (type_env [StructDecl "Empty" []])
    (ArrayT (StructT (NONE,"Empty")) (Dynamic 3))
    (AbiDynArray (AbiCopy 0) 0 0 F)
Proof
  rpt conj_tac >>
  ntac 7 (simp[Once abi_enc_plan_cases] >> EVAL_TAC >>
    simp[wordsTheory.dimword_def, valueEncodingTheory.type_memory_size_def])
QED
