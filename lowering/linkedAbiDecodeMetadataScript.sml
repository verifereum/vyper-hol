(* Supply the generic decoder metadata from the linked compiler tables. *)
Theory linkedAbiDecodeMetadata
Ancestors
  exprSimAbiDecodeEntryMetadata linkedStructFields linkedFlagCount
  abiCallerStructSize loweringStateRelDefs compileUnit compileEnv
  finite_map list pair

Theorem linked_abi_decode_root_metadata:
  contract_namespaces_ok dep mods /\
  ce.ce_struct_fields = make_struct_fields_map_mods mods /\
  ce.ce_flag_n_members = SND (build_flag_info_mods mods (K (K 0)) (K 0)) ==>
  abi_decode_root_metadata ce (type_env_all_modules mods)
Proof
  strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (type_env_all_modules mods)` by
    (drule make_struct_fields_map_mods_consistent >> simp[]) >>
  simp[abi_decode_root_metadata_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `sfields_tenv_consistent _ _`
        (strip_assume_tac o REWRITE_RULE [sfields_tenv_consistent_def]) >>
      `?nsid args. name = nsid_to_string nsid /\
          FLOOKUP (type_env_all_modules mods) nsid = SOME (StructArgs args)` by
        (qpat_assum `!key rows. FLOOKUP ce.ce_struct_fields key = _ ==> _`
           (qspecl_then [`name`,`fields`] mp_tac) >>
         simp[] >> metis_tac[]) >>
      drule_all make_struct_fields_map_mods_lookup >> strip_tac >>
      gvs[EVERY_MEM, FORALL_PROD] >>
      rpt strip_tac >> drule_all abi_caller_struct_field_sizes >> simp[]) >>
  rpt strip_tac >> drule_all linked_flag_member_count >> simp[]
QED
