(* TOP-LEVEL: actual compiler metadata encodes every evaluated, recursively
   typed source memory layout. Helpers compose fields, tuples and guarded
   named structs; array constructors use the complete default-filled layout. *)
Theory abiMemoryTypedEncoding
Ancestors
  abiMemoryTypedDefs abiMemoryTypedBase abiMemoryTypedFields abiMemoryTypedArray
  abiMemoryTypedFixed abiMemoryTypedStruct abiMemoryTypedMetadata abiMemoryTypedNative
  abiMemoryEncoding abiNativeEncoding abiTypeShape memoryValueAbiStatic memoryValueAbiTuple
  memoryValueDefs sourceAbiTypingLists exprLowering compileEnv valueEncoding
  vyperABI vyperValue vyperTyping vyperTypeValues vyperTypeABI
  finite_map contractABI list pair combin arithmetic

Definition abi_encoder_entry_def:
  abi_encoder_entry sfields cenv ty =
    (type_to_abi_enc_info sfields cenv ty, abi_embedded_static_size cenv.ce_struct_fields ty,
     type_memory_bytes cenv ty, is_abi_dynamic cenv.ce_struct_fields ty)
End

Theorem abi_typed_memory_cong:
  !env ty info other.
    abi_typed_memory env ty other /\
    (!tv. evaluate_type env ty = SOME tv ==> info = other) ==>
    abi_typed_memory env ty info
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_typed_memory_def] >>
  rpt gen_tac >> strip_tac >>
  `info = other` by (first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `info = other` SUBST1_TAC >>
  qpat_x_assum `abi_typed_memory env ty other` (mp_tac o REWRITE_RULE [abi_typed_memory_def]) >>
  disch_then (qspecl_then [`tv`, `v`, `av`, `source`, `span`, `mem`] mp_tac) >> simp[]
QED

Theorem abi_typed_encoder_cons_case:
  !env ty tys.
    ((!sfields cenv. abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
       abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty)) /\
     (!sfields cenv. abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
       abi_typed_fields env tys (MAP (abi_encoder_entry sfields cenv) tys))) ==>
    !sfields cenv. abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
      abi_typed_fields env (ty::tys) (MAP (abi_encoder_entry sfields cenv) (ty::tys))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC [MAP, abi_encoder_entry_def] >>
  irule abi_typed_fields_cons >> simp[] >> rpt strip_tac >>
  qspecl_then [`env`, `sfields`, `cenv`, `ty`, `tv`] mp_tac abi_typed_element_metadata >> simp[]
QED

Theorem abi_typed_encoder_tuple_case:
  !env tys.
    (!sfields cenv. abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
      abi_typed_fields env tys (MAP (abi_encoder_entry sfields cenv) tys)) ==>
    !sfields cenv. abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
      abi_typed_memory env (TupleT tys) (type_to_abi_enc_info sfields cenv (TupleT tys))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env (TupleT tys))`
  >- (qspecl_then [`env`, `TupleT tys`, `type_to_abi_enc_info sfields cenv (TupleT tys)`,
        `AbiComplex (MAP (abi_encoder_entry sfields cenv) tys)`] irule abi_typed_memory_cong >>
      conj_tac
      >- (qx_gen_tac `tv` >> DISCH_TAC >>
          qspecl_then [`env`, `TupleT tys`, `cenv.ce_struct_fields`, `tv`]
            mp_tac (CONJUNCT1 abi_type_dynamic_joint) >>
          impl_tac >- fs[abi_memory_env_rel_def] >> DISCH_TAC >>
          asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def] >>
          irule MAP_CONG >> simp[abi_encoder_entry_def]) >>
      irule abi_typed_fields_tuple >> simp[]) >>
  irule abi_typed_memory_static >> simp[]
QED

Theorem abi_typed_compiler_struct_info:
  !env sfields cenv nsid args.
    abi_struct_env_rel env sfields /\ FLOOKUP env nsid = SOME (StructArgs args) /\
    is_abi_dynamic cenv.ce_struct_fields (StructT nsid) ==>
    FST nsid = NONE /\
    type_to_abi_enc_info sfields cenv (StructT nsid) =
      AbiComplex (MAP (abi_encoder_entry (sfields \\ nsid_to_string nsid) cenv) (MAP SND args))
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_struct_env_rel_lookup >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def, LET_THM] >>
  qpat_x_assum `MAP (FST o SND) fields = MAP SND args` (SUBST1_TAC o SYM) >>
  simp_tac bool_ss [MAP_MAP_o] >> irule MAP_CONG >>
  simp[abi_encoder_entry_def, FORALL_PROD, o_DEF]
QED

Theorem type_memory_size_struct_zip:
  !args tvs.
    LENGTH args = LENGTH tvs ==>
    type_memory_size (StructTV (ZIP (MAP FST args,tvs))) = type_memory_size_list tvs
Proof
  rpt gen_tac >> DISCH_TAC >>
  `LENGTH (MAP FST args) = LENGTH tvs` by simp[] >>
  qpat_x_assum `LENGTH (MAP FST args) = LENGTH tvs` (fn th =>
    PURE_REWRITE_TAC [type_memory_size_def, type_memory_size_fields_list,
      CONJUNCT1 (CONJUNCT2 (MATCH_MP MAP_ZIP th))]) >> REFL_TAC
QED

Theorem abi_typed_encoder_struct_case:
  !env nsid.
    (!arg_kind args. FLOOKUP env nsid = SOME arg_kind /\ arg_kind = StructArgs args ==>
      !sfields cenv. abi_memory_env_rel (env \\ nsid) cenv /\ abi_struct_env_rel (env \\ nsid) sfields ==>
        abi_typed_fields (env \\ nsid) (MAP SND args) (MAP (abi_encoder_entry sfields cenv) (MAP SND args))) ==>
    !sfields cenv. abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
      abi_typed_memory env (StructT nsid) (type_to_abi_enc_info sfields cenv (StructT nsid))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `is_dynamic (vyper_to_abi_type env (StructT nsid))`)
  >- (irule abi_typed_memory_static >> simp[]) >>
  PURE_REWRITE_TAC [abi_typed_memory_def] >> rpt gen_tac >> strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields (StructT nsid)` by
    (qspecl_then [`env`, `StructT nsid`, `cenv.ce_struct_fields`, `tv`]
       mp_tac (CONJUNCT1 abi_type_dynamic_joint) >>
     impl_tac >- fs[abi_memory_env_rel_def] >> simp[]) >>
  qpat_x_assum `evaluate_type env (StructT nsid) = SOME tv`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs source_args)` >>
  rename1 `evaluate_types (env \\ nsid) (MAP SND source_args) [] = SOME field_tvs` >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs()] >>
  rename1 `memory_value_rel _ (StructV fields) source mem` >>
  rename1 `vyper_to_abi_list (env \\ nsid) (MAP SND source_args) (MAP SND fields) = SOME avs` >>
  qspecl_then [`env`, `sfields`, `cenv`, `nsid`, `source_args`] mp_tac abi_typed_compiler_struct_info >>
  impl_tac >- simp[] >> strip_tac >>
  `abi_memory_env_rel (env \\ nsid) cenv` by (irule abi_memory_env_rel_domsub >> simp[]) >>
  `abi_struct_env_rel (env \\ nsid) (sfields \\ nsid_to_string nsid)` by
    (irule abi_struct_env_rel_domsub >> simp[]) >>
  `abi_typed_fields (env \\ nsid) (MAP SND source_args)
     (MAP (abi_encoder_entry (sfields \\ nsid_to_string nsid) cenv) (MAP SND source_args))` by
    (first_x_assum drule_all >> simp[]) >>
  `LIST_REL (\ty tv. evaluate_type (env \\ nsid) ty = SOME tv) (MAP SND source_args) field_tvs` by
    (irule evaluate_types_LIST_REL >> simp[]) >>
  `LENGTH source_args = LENGTH field_tvs` by (drule LIST_REL_LENGTH >> simp[]) >>
  qspecl_then [`env \\ nsid`, `source_args`, `field_tvs`, `fields`, `avs`,
    `MAP (abi_encoder_entry (sfields \\ nsid_to_string nsid) cenv) (MAP SND source_args)`,
    `source`, `span`, `mem`] mp_tac abi_memory_typed_struct_fields >>
  fs[memory_value_rel_def, type_memory_size_struct_zip]
QED

Theorem abi_typed_encoding_joint:
  (!env ty. !sfields cenv.
    abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
    abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty)) /\
  (!env tys. !sfields cenv.
    abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields ==>
    abi_typed_fields env tys (MAP (abi_encoder_entry sfields cenv) tys))
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac >|
    [rpt strip_tac >> irule abi_typed_memory_base >> simp[],
     MATCH_ACCEPT_TAC abi_typed_encoder_tuple_case,
     rpt strip_tac >> irule abi_typed_memory_dynamic_array >> simp[],
     rpt strip_tac >> irule abi_typed_memory_fixed_array >> simp[],
     MATCH_ACCEPT_TAC abi_typed_encoder_struct_case,
     rpt strip_tac >> irule abi_typed_memory_flag >> simp[],
     simp[type_to_abi_enc_info_def, abi_typed_memory_none],
     simp[abi_typed_fields_nil],
     MATCH_ACCEPT_TAC abi_typed_encoder_cons_case]
QED

Theorem memory_value_rel_abi_encoding:
  !tops cenv ty tv v av source span reference.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    memory_value_rel tv v source reference /\ value_has_type tv v /\
    vyper_to_abi (type_env tops) ty v = SOME av /\ type_memory_size tv <= span ==>
    abi_memory_encoding (type_to_abi_enc_info cenv.ce_struct_fields cenv ty) source span reference
      (enc (vyper_to_abi_type (type_env tops) ty) av)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_memory_env_rel (type_env tops) cenv` by (irule abi_memory_env_rel_tops >> simp[]) >>
  `abi_struct_env_rel (type_env tops) cenv.ce_struct_fields` by
    (drule abi_struct_env_rel_tops >> simp[]) >>
  qspecl_then [`type_env tops`, `ty`, `cenv.ce_struct_fields`, `cenv`]
    mp_tac (CONJUNCT1 abi_typed_encoding_joint) >> impl_tac >- simp[] >>
  PURE_REWRITE_TAC [abi_typed_memory_def] >>
  disch_then (qspecl_then [`tv`, `v`, `av`, `source`, `span`, `reference`] mp_tac) >> simp[]
QED

Theorem abi_native_typed_encoding:
  !tops cenv ty tv v av source span reference.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    memory_value_rel tv v source reference /\ value_has_type tv v /\
    vyper_to_abi (type_env tops) ty v = SOME av /\ type_memory_size tv <= span ==>
    abi_native_encoder (type_to_abi_enc_info cenv.ce_struct_fields cenv ty) source span reference
      (enc (vyper_to_abi_type (type_env tops) ty) av)
Proof
  rpt gen_tac >> strip_tac >> drule_all memory_value_rel_abi_encoding >> DISCH_TAC >>
  drule (CONJUNCT1 abi_native_encoding) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete typed ABI memory encoding: " ^ name)
  end) (DB.thms "abiMemoryTypedEncoding")
