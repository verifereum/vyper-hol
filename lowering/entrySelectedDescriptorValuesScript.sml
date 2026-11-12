Theory entrySelectedDescriptorValues
Ancestors
  entrySelectedPackageCoherence entrySelectedAbiTyping entryPackageDescriptorFacts
  entrySelectedSourceCardinality entryExternalPackageCoherence
  abiTupleValueEncoding abiDecoderCoherence compileVyper compileEnv exprLowering
  vyperABIRoundtrip vyperABI vyperTyping list rich_list pair

Theorem source_conversion_values[local]:
  !tys vs avs.
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v)
    tys vs /\
  LIST_REL (\ty va. vyper_to_abi env ty (FST va) = SOME (SND va))
    tys (ZIP (vs,avs)) /\ LENGTH avs = LENGTH vs ==>
  ?values.
    LIST_REL (\ty (ty',tv,v,at,av).
      ty' = ty /\ evaluate_type env ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env ty v = SOME av /\ at = vyper_to_abi_type env ty)
      tys values /\
    MAP (\(ty,tv,v,at,av). v) values = vs /\
    MAP (\(ty,tv,v,at,av). at) values = vyper_to_abi_types env tys /\
    MAP (\(ty,tv,v,at,av). av) values = avs
Proof
  Induct >> Cases_on `vs` >> Cases_on `avs` >>
  simp[vyper_to_abi_type_def] >> rpt strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `evaluate_type env ty = SOME tv` >>
  rename1 `vyper_to_abi env ty v = SOME av` >>
  qexists `(ty,tv,v,vyper_to_abi_type env ty,av)::values` >> simp[]
QED

Theorem source_conversion_values_from_call[local]:
  LIST_REL (\ty v. assignable_type env ty /\
    ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  ?values.
    LIST_REL (\ty (ty',tv,v,at,av).
      ty' = ty /\ evaluate_type env ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env ty v = SOME av /\ at = vyper_to_abi_type env ty)
      tys values /\
    MAP (\(ty,tv,v,at,av). v) values = vs /\
    MAP (\(ty,tv,v,at,av). at) values = vyper_to_abi_types env tys /\
    MAP (\(ty,tv,v,at,av). av) values = avs
Proof
  strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >>
  irule source_conversion_values >>
  gvs[LIST_REL_EL_EQN, EL_ZIP] >> metis_tac[]
QED

Theorem coherent_descriptor_value[local]:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv ==>
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  (is_word_type ty ==> ?c. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord c) /\
  (is_abi_dynamic ce.ce_struct_fields ty /\ ~is_word_type ty <=>
    is_dynamic (vyper_to_abi_type env ty))
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  `is_word_type ty ==> ?c.
    type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord c` by
    (Cases_on `ty` >> simp[is_word_type_def, type_to_abi_dec_info_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_word_type_def, type_to_abi_dec_info_def] >>
     rename1 `BytesT b` >> Cases_on `b` >>
     simp[is_word_type_def, type_to_abi_dec_info_def]) >>
  metis_tac[abi_word_metadata]
QED

Theorem descriptor_values_transport[local]:
  LIST_REL (\ty (ty',tv,v,at,av).
    ty' = ty /\ evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ at = vyper_to_abi_type env ty)
    (MAP SND args) values /\
  (!name ty tv. MEM (name,ty) args /\ evaluate_type env ty = SOME tv ==>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv) ==>
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ evaluate_type env ty = SOME tv) args values /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\
    sz = abi_member_head_size at /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\
    (dyn /\ ~prim <=> is_dynamic at) /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ at = vyper_to_abi_type env ty)
    (build_positional_args ce args) values
Proof
  strip_tac >>
  `LIST_REL (\(name,ty) (name',prim,dyn,sz,info).
    name' = name /\ prim = is_word_type ty /\
    dyn = is_abi_dynamic ce.ce_struct_fields ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\
    info = type_to_abi_dec_info ce.ce_struct_fields ce ty)
    args (build_positional_args ce args)` by
      simp[build_positional_args_source_relation] >>
  gvs[LIST_REL_EL_EQN, EL_MAP] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n. _ ==> (\(ty',tv,v,at,av). _) _`
        (qspec_then `n` mp_tac) >> simp[] >>
      qabbrev_tac `arg = EL n args` >>
      qabbrev_tac `value = EL n values` >>
      PairCases_on `arg` >> PairCases_on `value` >> simp[]) >>
  rpt strip_tac >>
  `MEM (FST (EL n args),SND (EL n args)) args` by
    (simp[] >> irule EL_MEM >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >>
  qpat_x_assum `!n. _ ==> (\(ty',tv,v,at,av). _) _`
    (qspec_then `n` mp_tac) >> simp[] >>
  qabbrev_tac `arg = EL n args` >>
  qabbrev_tac `value = EL n values` >>
  qabbrev_tac `spec = EL n (build_positional_args ce args)` >>
  PairCases_on `arg` >> PairCases_on `value` >> PairCases_on `spec` >>
  simp[] >> ntac 2 strip_tac >> gvs[] >>
  `abi_decoder_coherent ce env ce.ce_struct_fields arg1 value1` by
    metis_tac[] >>
  drule coherent_descriptor_value >> simp[]
QED

Theorem selected_external_descriptor_values:
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  ?values.
    LIST_REL (\(name,ty) (ty',tv,v,at,av).
      ty' = ty /\ evaluate_type (type_env tops) ty = SOME tv) args values /\
    MAP (\(ty,tv,v,at,av). v) values = tx.args /\
    LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
      sz = abi_embedded_static_size ce.ce_struct_fields ty /\
      sz = abi_member_head_size at /\
      type_memory_bytes ce ty = type_memory_size tv /\
      (prim ==> ?c. info = DecPrimWord c) /\
      (dyn /\ ~prim <=> is_dynamic at) /\ value_has_type tv v /\
      vyper_to_abi (type_env tops) ty v = SOME av /\
      at = vyper_to_abi_type (type_env tops) ty) specs values /\
    has_types (MAP (\(ty,tv,v,at,av). at) values)
      (MAP (\(ty,tv,v,at,av). av) values) /\
    vs.vs_call_ctx.cc_calldata =
      function_selector tx.function_name (MAP (\(ty,tv,v,at,av). at) values) ++
      enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
        (ListV (MAP (\(ty,tv,v,at,av). av) values))
Proof
  strip_tac >> drule_all selected_call_abi_values_typed >> strip_tac >>
  drule_all selected_call_source_values >> strip_tac >>
  drule_all source_conversion_values_from_call >> strip_tac >>
  drule external_package_layout >> strip_tac >>
  `!name ty tv. MEM (name,ty) args /\
    evaluate_type (type_env tops) ty = SOME tv ==>
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv` by
    (rpt strip_tac >> irule selected_external_package_decoder_coherent >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all descriptor_values_transport >> strip_tac >>
  qexists `values` >> gvs[]
QED
