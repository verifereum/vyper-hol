Theory externalReturnZeroSource
Ancestors
  externalReturnZeroLayout externalReturnSelectedMetadata externalNormalizePremises
  valueCopyBytes structFieldsProps typedCopyProducer supportedReturnAbiMetadata
  compileVyper exprLowering loweringPosts valueEncoding vyperTypeSystem
  vyperTyping vyperValue e2eDefs vyperTypeContract vyperTypeContractStaticMaps
  vyperContext

Theorem typed_zero_return_layout:
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  val_footprint tv v = 0 /\
  (ty = ret \/ is_bytestring_type ty /\ is_bytestring_type ret) ==>
  ty = ret /\ ~is_bytestring_type ty /\ type_memory_size tv = 0
Proof
  strip_tac >>
  `~is_bytestring_type ty` by
    (strip_tac >> drule_all bytestring_type_value >> strip_tac >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]) >>
  `ty = ret` by metis_tac[] >>
  drule_all normalize_nonbytes_footprint >> simp[]
QED

Theorem selected_external_zero_source_metadata:
  !tops am tx name mut nr args ret fbody target use_trans keys
   rr pkg_defaults lbl cenv0 pos_args min_cds payable nr' key ut iv fbody' rt
   off st cenv sa c env e ty tv v.
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,pkg_defaults,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr',key,ut,iv,fbody',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv c /\ IS_SOME (type_stmt env ret (Return (SOME e))) /\
  evaluate_type
    (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)) ty = SOME tv /\
  value_has_type tv v /\ val_footprint tv v = 0 /\
  (ty = ret \/ is_bytestring_type ty /\ is_bytestring_type ret) ==>
  c.ce_ret_enc_info = AbiCopy 0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_zero_return_layout >> strip_tac >>
  drule externalReturnAbiMetadataTheory.source_deployment_return_tenv >> strip_tac >>
  `evaluate_type (type_env tops) ret = SOME tv` by metis_tac[] >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    (qpat_x_assum `source_typing_ok _ _ _` mp_tac >>
     rw[source_typing_ok_def, check_contract_def] >>
     drule contract_namespaces_ok_module_type_def_keys >> simp[]) >>
  qabbrev_tac `cebase = build_compile_env tops External mut name args ret fbody use_trans` >>
  `cebase.ce_struct_fields = make_struct_fields_map tops` by
    simp[Abbr `cebase`, build_compile_env_ce_struct_fields] >>
  `sfields_tenv_consistent cebase.ce_struct_fields (type_env tops)` by
    simp[make_struct_fields_map_consistent] >>
  `!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE` by
    (rw[type_env_def] >> drule type_env_for_module_struct_mem >> rw[] >> simp[]) >>
  `struct_args_unique tops` by
    (irule distinct_type_keys_struct_args_unique >> simp[]) >>
  `type_memory_bytes cebase ret = type_memory_size tv` by
    (drule_all make_struct_fields_map_memory_size >> simp[]) >>
  `cebase = build_compile_env tops External mut name args ret fbody use_trans` by
    simp[Abbr `cebase`] >>
  drule_all external_package_zero_layout_encoder >> simp[]
QED
