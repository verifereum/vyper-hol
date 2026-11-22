(* A checked public getter has only single-word ABI heads. *)
Theory defaultDispatchModsSize
Ancestors
  e2eModsDefs compileUnit compileEnv compileVyper
  vyperABIEntries vyperCalldata vyperTypeContractStaticMaps
  vyperTypeContract vyperTypeSystem vyperTypeConversions vyperValue list pair

Triviality getter_key_head_size[local]:
  hashmap_key_type ty /\ evaluate_type tenv ty = SOME tv ==>
  abi_embedded_static_size fields ty = tv_abi_size tv
Proof
  Cases_on `ty` >> gvs[hashmap_key_type_def]
  >- (strip_tac >> drule evaluate_type_BaseT_SOME >> strip_tac >> gvs[] >>
      Cases_on `b` >> simp[abi_embedded_static_size_def, is_abi_dynamic_def,
        abi_static_size_def, tv_abi_size_def, tv_abi_dynamic_def,
        tv_abi_static_size_def] >>
      Cases_on `b'` >> simp[abi_embedded_static_size_def, is_abi_dynamic_def,
        abi_static_size_def, tv_abi_size_def, tv_abi_dynamic_def,
        tv_abi_static_size_def]) >>
  rw[evaluate_type_def, AllCaseEqs()] >>
  gvs[abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
      tv_abi_size_def, tv_abi_dynamic_def, tv_abi_static_size_def]
QED

Triviality array_getter_keys[local]:
  !ty. EVERY hashmap_key_type (abi_array_getter_args ty)
Proof
  recInduct abi_array_getter_args_ind >>
  simp[abi_array_getter_args_def, hashmap_key_type_def]
QED

Triviality checked_map_getter_keys[local]:
  !vt. check_value_type tenv vt ==>
       EVERY hashmap_key_type (abi_getter_args vt)
Proof
  Induct >> simp[check_value_type_def, abi_getter_args_def, array_getter_keys]
QED

Triviality checked_default_signature_keys[local]:
  !top. check_toplevel_decl mods art src top /\
        MEM ("__default__", tys) (abi_decl_signatures top) ==>
        EVERY hashmap_key_type tys
Proof
  Cases >> simp[abi_decl_signatures_def] >> rpt gen_tac
  >- (Cases_on `f` >> simp[abi_decl_signatures_def] >>
      IF_CASES_TAC >> simp[abi_function_signatures_def, MEM_MAP, EXISTS_PROD])
  >- (Cases_on `v` >> simp[abi_decl_signatures_def, array_getter_keys]) >>
  Cases_on `v` >>
  simp[abi_decl_signatures_def, check_toplevel_decl_def] >>
  metis_tac[checked_map_getter_keys]
QED

Triviality getter_keys_head_sum[local]:
  !tys tvs. EVERY hashmap_key_type tys /\
      OPT_MMAP (evaluate_type tenv) tys = SOME tvs ==>
      SUM (MAP (abi_embedded_static_size fields) tys) =
      SUM (MAP tv_abi_size tvs)
Proof
  Induct >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >>
  gvs[] >> drule_all getter_key_head_size >> simp[]
QED

Theorem default_getter_package_min_size:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods src = SOME tops /\ MEM top tops /\
  MEM ("__default__",MAP SND args) (abi_decl_signatures top) /\
  OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND args) = SOME tvs /\
  set_external_package_target target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,(mut,nr,rr,"__default__",args,([]:expr list),ret,fbody))) =
    (lbl,ce,pa,mc,pay,nr,key,ut,iv,fbody,rt) ==>
  mc = 4 + SUM (MAP tv_abi_size tvs)
Proof
  strip_tac >>
  `EVERY hashmap_key_type (MAP SND args)` by
    (fs[source_typing_ok_mods_def] >>
     drule_all check_contract_toplevel_decl_MEM >>
     metis_tac[checked_default_signature_keys]) >>
  `mc = min_calldata_size ce args 0` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_unit_def, set_external_package_target_def] >>
     rpt strip_tac >> gvs[min_calldata_size_def]) >>
  `SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) (MAP SND args)) =
   SUM (MAP tv_abi_size tvs)` by metis_tac[getter_keys_head_sum] >>
  pop_assum mp_tac >>
  simp[min_calldata_size_def, ELIM_UNCURRY, MAP_MAP_o, combinTheory.o_DEF]
QED
