(* Source environments and actual external-return ABI metadata. *)
Theory externalReturnAbiMetadata
Ancestors
  exprLowering compileEnv abiEncoderProps abiEncoderSourceProducer
  externalReturnZeroLayout externalRawReturnType retAbiPlanProps
  typedNormalizeProducer supportedProgram supportedTypes
  supportedReturnAbiMetadata compileVyper entryStateRel bodySim
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

Theorem external_package_frame_abi_metadata:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_place_type tops ret /\ evaluate_type (type_env tops) ret = SOME tv /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr',key,ut,iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv c ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) c.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = c.ce_max_return_size
Proof
  strip_tac >>
  `ret <> NoneT` by
    (spose_not_then assume_tac >>
     gvs[supported_place_type_def, Once supported_nested_type_def,
         supported_scalar_type_def, supported_word_type_def,
         supported_string_type_def]) >>
  `abi_enc_plan (type_env tops)
     (if needs_external_call_wrap ret /\
         is_dynamic (vyper_to_abi_type (type_env tops) ret)
      then TupleT [ret] else ret)
     (update_cenv_ret_abi
       (build_compile_env tops External mut name args ret fbody use_trans
        with ce_raw_return := rr) ret).ce_ret_enc_info /\
   vyper_abi_size_bound (type_env tops)
     (if needs_external_call_wrap ret /\
         is_dynamic (vyper_to_abi_type (type_env tops) ret)
      then TupleT [ret] else ret) =
     (update_cenv_ret_abi
       (build_compile_env tops External mut name args ret fbody use_trans
        with ce_raw_return := rr) ret).ce_max_return_size` by
    (irule supported_update_cenv_ret_abi_plan >>
     simp[build_compile_env_ce_struct_fields] >> metis_tac[]) >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST_ALL_TAC >>
  fs[same_frame_def, compile_env_component_equality]
QED

Theorem external_package_frame_source_abi_metadata:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_place_type tops ret /\ evaluate_type (type_env tops) ret = SOME tv /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr',key,ut,iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv c /\ source_deployment_rel tops am tx ==>
  abi_enc_plan (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type
          (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)) ret)
     then TupleT [ret] else ret) c.ce_ret_enc_info /\
  vyper_abi_size_bound
    (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type
          (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)) ret)
     then TupleT [ret] else ret) = c.ce_max_return_size
Proof
  strip_tac >> drule source_deployment_return_tenv >> strip_tac >> simp[] >>
  irule external_package_frame_abi_metadata >> metis_tac[]
QED
