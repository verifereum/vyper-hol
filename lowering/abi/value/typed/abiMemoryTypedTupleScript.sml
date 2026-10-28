(* TOP-LEVEL: actual tuple encoder metadata works for complete typed field
   lists. Synthetic log tuples need no separate source TupleT evaluation or
   fixed field family. Helpers recover compiler sizes and dynamic flags. *)
Theory abiMemoryTypedTuple
Ancestors
  abiMemoryTypedEncoding abiMemoryTypedDefs abiMemoryTypedMetadata abiMemoryEncoding
  abiNativeEncoding abiFieldSource abiFieldPackedStaticSizes abiTypeShape typeLayoutProps
  memoryValueDefs memoryValueAbiTuple exprLowering compileEnv valueEncoding
  vyperABI vyperValue vyperTyping contractABI list pair arithmetic

Theorem abi_memory_env_rel_list_sizes:
  !tys tvs env cenv.
    abi_memory_env_rel env cenv /\ LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
    MAP (type_memory_bytes cenv) tys = MAP type_memory_size tvs
Proof
  Induct_on `tys` >- (Cases_on `tvs` >> simp[]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  qmatch_goalsub_rename_tac
    `MAP (type_memory_bytes cenv) (head_ty::rest_tys) = MAP type_memory_size (head_tv::rest_tvs)` >>
  simp[] >> strip_tac >>
  `type_memory_bytes cenv head_ty = type_memory_size head_tv` by
    (fs[abi_memory_env_rel_def] >> first_x_assum drule_all >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_evaluated_tuple_shape:
  !env cenv tys tvs.
    abi_memory_env_rel env cenv /\ LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    is_abi_dynamic cenv.ce_struct_fields (TupleT tys) =
      EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_env_rel_list_sizes >> DISCH_TAC >>
  `abi_struct_env_rel env cenv.ce_struct_fields` by fs[abi_memory_env_rel_def] >>
  qspecl_then [`env`, `tys`, `cenv.ce_struct_fields`, `tvs`]
    mp_tac (CONJUNCT2 abi_type_dynamic_joint) >> impl_tac >- simp[] >> DISCH_TAC >>
  `EXISTS (is_abi_dynamic cenv.ce_struct_fields) tys =
   EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys` by
    (irule abi_dynamic_exists >> simp[]) >> conj_tac
  >- (simp_tac bool_ss [type_memory_bytes_def, type_memory_size_list_sum] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss []) >>
  PURE_ONCE_REWRITE_TAC [is_abi_dynamic_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_evaluated_tuple_encoder:
  !env sfields cenv tys tvs.
    abi_memory_env_rel env cenv /\ LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
    type_to_abi_enc_info sfields cenv (TupleT tys) =
      if EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys then
        AbiComplex (MAP (abi_encoder_entry sfields cenv) tys)
      else AbiCopy (type_memory_size_list tvs)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_evaluated_tuple_shape >> strip_tac >>
  Cases_on `EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys` >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def] >>
  irule MAP_CONG >> simp[abi_encoder_entry_def]
QED

Theorem abi_memory_typed_tuple:
  !env sfields cenv tys tvs vs avs source span mem.
    abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    memory_tuple_rel tvs vs source mem /\ values_have_types tvs vs /\
    vyper_to_abi_list env tys vs = SOME avs /\ type_memory_size_list tvs <= span ==>
    abi_memory_encoding (type_to_abi_enc_info sfields cenv (TupleT tys)) source span mem
      (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))
Proof
  rpt gen_tac >> strip_tac >>
  `abi_typed_fields env tys (MAP (abi_encoder_entry sfields cenv) tys)` by
    (qspecl_then [`env`, `tys`, `sfields`, `cenv`] mp_tac (CONJUNCT2 abi_typed_encoding_joint) >> simp[]) >>
  `abi_memory_fields (MAP (abi_encoder_entry sfields cenv) tys) source span mem
     (MAP2 (\ty av. (is_dynamic ty, enc ty av)) (MAP (vyper_to_abi_type env) tys) avs)` by
    (qpat_x_assum `abi_typed_fields env tys _` (mp_tac o REWRITE_RULE [abi_typed_fields_def]) >>
     disch_then (qspecl_then [`tvs`, `vs`, `avs`, `source`, `span`, `mem`] mp_tac) >> simp[]) >>
  `LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty)
     (MAP (vyper_to_abi_type env) tys) avs` by
    (qspecl_then [`tys`, `env`, `tvs`, `vs`, `avs`, `source`, `mem`]
       mp_tac memory_tuple_source_static_sizes >> simp[]) >>
  `abi_memory_encoding (AbiComplex (MAP (abi_encoder_entry sfields cenv) tys)) source span mem
     (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))` by
    (drule enc_tuple_head_size >> disch_then SUBST1_TAC >>
     irule abi_memory_encoding_complex >> simp[]) >>
  `~EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys ==>
   abi_memory_encoding (AbiCopy (type_memory_size_list tvs)) source span mem
     (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))` by
    (DISCH_TAC >> qspecl_then [`env`, `tys`, `tvs`, `vs`, `avs`, `source`, `mem`]
       mp_tac memory_tuple_static_source_bytes >> impl_tac >- fs[EVERY_MEM, EXISTS_MEM] >> strip_tac >>
     qpat_x_assum `mem_bytes_at _ _ _ = _` (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     irule abi_memory_encoding_copy >> simp[]) >>
  qspecl_then [`env`, `sfields`, `cenv`, `tys`, `tvs`] mp_tac abi_evaluated_tuple_encoder >>
  impl_tac >- simp[] >> DISCH_TAC >>
  Cases_on `EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys` >> asm_simp_tac bool_ss []
QED

Theorem abi_native_typed_tuple:
  !env sfields cenv tys tvs vs avs source span reference.
    abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    memory_tuple_rel tvs vs source reference /\ values_have_types tvs vs /\
    vyper_to_abi_list env tys vs = SOME avs /\ type_memory_size_list tvs <= span ==>
    abi_native_encoder (type_to_abi_enc_info sfields cenv (TupleT tys)) source span reference
      (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_typed_tuple >> DISCH_TAC >>
  drule (CONJUNCT1 abi_native_encoding) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed synthetic typed ABI tuple: " ^ name)
  end) (DB.thms "abiMemoryTypedTuple")
