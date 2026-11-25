Theory dispatchedSignatureOriginMods
Ancestors
  alist list pair compileUnit e2eModsDefs defaultDispatchModsNames
  vyperABIEntries vyperTypeContract

Theorem abi_decl_signature_external_key:
  !top src name tys.
    MEM (name,tys) (abi_decl_signatures top) ==>
    MEM (src,name) (external_name_keys_toplevel src top)
Proof
  Cases >> simp[abi_decl_signatures_def, external_name_keys_toplevel_def] >>
  rpt gen_tac
  >- (Cases_on `f` >> simp[abi_decl_signatures_def, external_name_keys_toplevel_def] >>
      IF_CASES_TAC >> rw[abi_function_signatures_def,MEM_MAP,EXISTS_PROD] >> gvs[]) >>
  Cases_on `v` >> simp[abi_decl_signatures_def, external_name_keys_toplevel_def]
QED

Theorem deployed_signature_selected_module:
  source_typing_ok_mods mods exps am tx /\
  MEM (name,tys) (abi_deployed_signatures mods exps) ==>
  ?tops top. ALOOKUP mods (ALOOKUP exps name) = SOME tops /\
             MEM top tops /\ MEM (name,tys) (abi_decl_signatures top)
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `MEM _ (abi_deployed_signatures _ _)` mp_tac >>
  simp[abi_deployed_signatures_def,MEM_FLAT,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
  strip_tac
  >- (Cases_on `ALOOKUP mods NONE` >> gvs[] >>
      rename1 `ALOOKUP mods NONE = SOME main` >>
      fs[abi_external_signatures_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      `MEM (NONE:num option,name)
        (FLAT (MAP (external_name_keys_toplevel NONE) (main_module mods)))` by
        (simp[main_module_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
         metis_tac[abi_decl_signature_external_key]) >>
      `ALOOKUP exps name = NONE` by
        (simp[ALOOKUP_NONE] >> metis_tac[export_excludes_main_external]) >>
      gvs[] >> metis_tac[]) >>
  rename1 `MEM (nm,s) exps` >>
  Cases_on `ALOOKUP mods (SOME s)` >> gvs[MEM_FILTER] >>
  `ALL_DISTINCT (MAP FST exps)` by
    (fs[source_typing_ok_mods_def] >> metis_tac[exports_ok_names]) >>
  `ALOOKUP exps name = SOME s` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  gvs[abi_external_signatures_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >> metis_tac[]
QED

Theorem deployed_signature_selected_decl:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\
  MEM (name,tys) (abi_deployed_signatures mods exps) ==>
  ?top. MEM top tops /\ MEM (name,tys) (abi_decl_signatures top)
Proof
  strip_tac >> drule_all deployed_signature_selected_module >> simp[]
QED
