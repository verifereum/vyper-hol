(* Qualified struct traversal for Log. The shrinking field map is for
   recursion only; size metadata is always read in the full compile env. *)
Theory bodyLogAbiLayoutMods
Ancestors
  bodyInvMetadataProps exprSimHypsDefs exprSimAbiEncodePlanMetadata
  typedMemoryCopy linkedNsidProps structFieldsProps
  vyperTypeContract vyperTypeConstantFold vyperContext
  abiDecodeRanges compileEnv loweringStateRelDefs finite_map alist list pair

Theorem log_struct_lookup_dot_free[local]:
  contract_namespaces_ok dep mods /\
  FLOOKUP (type_env_all_modules mods) k = SOME (StructArgs args) ==>
  ~MEM #"." (SND k)
Proof
  PairCases_on `k` >> simp[] >> strip_tac >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  drule_then (qspecl_then [`k0`,`k1`] assume_tac) FLOOKUP_type_env_all_modules >>
  Cases_on `ALOOKUP mods k0` >> gvs[] >>
  drule_then strip_assume_tac type_env_for_module_struct_mem >> gvs[] >>
  drule_then assume_tac ALOOKUP_MEM >>
  qpat_x_assum `contract_namespaces_ok _ _`
    (strip_assume_tac o REWRITE_RULE [contract_namespaces_ok_def]) >>
  qpat_x_assum `EVERY (\(_,xs). EVERY _ xs) mods` mp_tac >>
  simp[Once EVERY_MEM] >>
  rename1 `MEM (src,tops) mods` >>
  disch_then (qspec_then `(src,tops)` mp_tac) >> simp[Once EVERY_MEM] >>
  rename1 `MEM (StructDecl name args) tops` >>
  disch_then (qspec_then `StructDecl name args` mp_tac) >> simp[]
QED

Theorem log_abi_delete_lookup[local]:
  !ks fm k.
    FLOOKUP (FOLDR (\j m. m \\ j) fm ks) k =
      if MEM k ks then NONE else FLOOKUP fm k
Proof
  Induct >> simp[DOMSUB_FLOOKUP_THM] >> metis_tac[]
QED

Theorem log_abi_delete_printed_lookup[local]:
  !ks sf n. FLOOKUP (FOLDR (\j m. m \\ nsid_to_string j) sf ks) n =
             if MEM n (MAP nsid_to_string ks) then NONE else FLOOKUP sf n
Proof
  rpt gen_tac >>
  qspecl_then [`MAP nsid_to_string ks`,`sf`,`n`] mp_tac log_abi_delete_lookup >>
  simp[rich_listTheory.FOLDR_MAP]
QED

Theorem log_abi_printed_delete[local]:
  contract_namespaces_ok dep mods /\
  EVERY (\j. ?ds. FLOOKUP (type_env_all_modules mods) j = SOME (StructArgs ds)) ks /\
  FLOOKUP (type_env_all_modules mods) k = SOME (StructArgs args) ==>
  (MEM (nsid_to_string k) (MAP nsid_to_string ks) <=> MEM k ks)
Proof
  simp[EVERY_MEM, MEM_MAP] >> strip_tac >> iff_tac
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      metis_tac[log_struct_lookup_dot_free, nsid_to_string_dot_free_injective]) >>
  metis_tac[]
QED

Theorem log_abi_deleted_fields[local]:
  contract_namespaces_ok dep mods /\
  sfields_tenv_consistent sf (type_env_all_modules mods) /\
  EVERY (\j. ?ds. FLOOKUP (type_env_all_modules mods) j = SOME (StructArgs ds)) ks ==>
  sfields_tenv_consistent (FOLDR (\j m. m \\ nsid_to_string j) sf ks)
    (FOLDR (\j m. m \\ j) (type_env_all_modules mods) ks)
Proof
  strip_tac >> qpat_x_assum `sfields_tenv_consistent _ _`
    (strip_assume_tac o REWRITE_RULE [sfields_tenv_consistent_def]) >>
  simp[sfields_tenv_consistent_def, log_abi_delete_lookup,
       log_abi_delete_printed_lookup] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all log_abi_printed_delete >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all log_abi_printed_delete >> simp[] >> metis_tac[]
QED

Theorem log_abi_layout_metadata_mods:
  contract_inv mods exps ctx ce cx /\
  contract_namespaces_ok dep mods /\
  expr_sim_inv_mods mods ce cx env es ==>
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
           type_memory_bytes ce ty = type_memory_size tv) /\
  (!ks. EVERY (\j. ?args. FLOOKUP (get_tenv cx) j = SOME (StructArgs args)) ks ==>
    sfields_tenv_consistent
      (FOLDR (\j m. m \\ nsid_to_string j) ce.ce_struct_fields ks)
      (FOLDR (\j m. m \\ j) (get_tenv cx) ks)) /\
  (!E ty tv. E SUBMAP get_tenv cx /\ evaluate_type E ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv /\
    abi_embedded_static_size ce.ce_struct_fields ty =
      abi_member_head_size (vyper_to_abi_type E ty) /\
    is_abi_dynamic ce.ce_struct_fields ty = is_dynamic (vyper_to_abi_type E ty) /\
    abi_size_bound ce.ce_struct_fields ty = vyper_abi_size_bound (get_tenv cx) ty)
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_type_env >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
           type_memory_bytes ce ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists `get_tenv cx` >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `get_tenv cx = _` SUBST_ALL_TAC >>
      irule log_abi_deleted_fields >> simp[] >>
      qexists `dep` >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_element_metadata >> simp[abi_member_head_size_def]
QED
