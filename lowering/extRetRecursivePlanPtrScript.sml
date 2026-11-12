Theory extRetRecursivePlanPtr
Ancestors vyperValue valueEncoding retAbiPlanProps abiEncoderProps compileEnv exprLowering vyperTyping finite_map list rich_list

Inductive encodable_ret_shape:
[base:]
  evaluate_type tenv (BaseT bt) = SOME tv ==>
  encodable_ret_shape tenv (BaseT bt)
[flag:]
  evaluate_type tenv (FlagT id) = SOME tv ==>
  encodable_ret_shape tenv (FlagT id)
[array:]
  evaluate_type tenv (ArrayT t bd) = SOME tv /\
  encodable_ret_shape tenv t ==>
  encodable_ret_shape tenv (ArrayT t bd)
[tuple:]
  evaluate_type tenv (TupleT ts) = SOME tv /\
  EVERY (encodable_ret_shape tenv) ts ==>
  encodable_ret_shape tenv (TupleT ts)
[record_shape:]
  FLOOKUP tenv id = SOME (StructArgs fields) /\
  evaluate_type tenv (StructT id) = SOME tv /\
  EVERY (\field. encodable_ret_shape (tenv \\ id) (SND field)) fields ==>
  encodable_ret_shape tenv (StructT id)
End

Theorem encodable_ret_shape_evaluates:
  !tenv ty. encodable_ret_shape tenv ty ==>
    ?tv. evaluate_type tenv ty = SOME tv
Proof
  rpt strip_tac >>
  gvs[Once encodable_ret_shape_cases] >> metis_tac[]
QED

Theorem map_return_field_types[local]:
  !fields. MAP (\(fn,fty,sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >> simp[]
QED

Theorem encodable_ret_shape_plan:
  !tenv ty. encodable_ret_shape tenv ty ==>
  !sf cenv tenv0.
    tenv SUBMAP tenv0 /\
    sfields_tenv_consistent sf tenv /\
    (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
    (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type tenv0 t = SOME tv ==>
       type_memory_bytes cenv t = type_memory_size tv) ==>
    abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)
Proof
  ho_match_mp_tac encodable_ret_shape_strongind >> rpt conj_tac
  >- (((rpt strip_tac >> Cases_on `bt` >>
         simp[type_to_abi_enc_info_def, abi_enc_plan_bytes, abi_enc_plan_string])
        >~ [`BytesT bd`]
        >- (Cases_on `bd` >>
            simp[type_to_abi_enc_info_def, abi_enc_plan_bytes] >>
            irule abi_enc_plan_static_copy >> simp[is_abi_dynamic_def] >>
            metis_tac[]) >>
        irule abi_enc_plan_static_copy >> simp[is_abi_dynamic_def] >>
        metis_tac[]))
  >- (rpt strip_tac >> simp[type_to_abi_enc_info_def] >>
      irule abi_enc_plan_static_copy >> simp[is_abi_dynamic_def] >>
      metis_tac[])
  >- (rpt strip_tac >>
      drule encodable_ret_shape_evaluates >> strip_tac >>
      `abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)` by
        (first_x_assum irule >> metis_tac[]) >>
      Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
      >- (IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
          simp[GSYM REPLICATE_GENLIST] >>
          drule_all abi_elem_props >> strip_tac >>
          irule abi_enc_plan_sarray >> gvs[is_abi_dynamic_def] >>
          drule_all abi_enc_plans_replicate >>
          disch_then (qspec_then `n` mp_tac) >> gvs[]) >>
      drule_all abi_elem_props >> strip_tac >> simp[] >>
      irule abi_enc_plan_dynarray >> simp[])
  >- (rpt strip_tac >> simp[Once type_to_abi_enc_info_def] >>
      IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
      drule_all abi_elem_props >> strip_tac >>
      irule abi_enc_plan_tuple >>
      conj_tac >- gvs[vyperABITheory.vyper_to_abi_type_def,
                      contractABITheory.is_dynamic_def] >>
      irule abi_enc_plans_map >>
      reverse conj_tac >- (qexists `tenv0` >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `EVERY _ ts` mp_tac >> simp[EVERY_MEM] >>
      disch_then drule >> strip_tac >>
      drule encodable_ret_shape_evaluates >> strip_tac >>
      simp[] >> first_x_assum irule >> metis_tac[])
  >> rpt strip_tac >> simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
  `?fs. FLOOKUP sf (nsid_to_string id) = SOME fs /\
         MAP (FST o SND) fs = MAP SND fields` by
    (qpat_x_assum `sfields_tenv_consistent sf tenv` mp_tac >>
     simp[sfields_tenv_consistent_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> simp[]) >>
  drule_all abi_elem_props >> strip_tac >>
  simp[map_return_field_types] >>
  irule abi_enc_plan_struct >>
  drule_all sfields_tenv_consistent_domsub >> strip_tac >>
  simp[] >> conj_tac
  >- gvs[vyperABITheory.vyper_to_abi_type_def,
         contractABITheory.is_dynamic_def] >>
  irule abi_enc_plans_map >>
  reverse conj_tac
  >- (qexists `tenv0` >> simp[] >>
      fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      rpt strip_tac >> first_x_assum irule >> gvs[]) >>
  rpt strip_tac >>
  gvs[MEM_MAP] >>
  qpat_x_assum `EVERY _ fields` mp_tac >> simp[EVERY_MEM] >>
  disch_then drule >> strip_tac >>
  drule encodable_ret_shape_evaluates >> strip_tac >>
  simp[] >> first_x_assum irule >> simp[] >>
  qexists `tenv0` >> simp[] >>
  fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  rpt strip_tac >> first_x_assum irule >> gvs[]
QED

Theorem encodable_ret_shape_empty_struct:
  FLOOKUP tenv id = SOME (StructArgs []) /\
  evaluate_type tenv (StructT id) = SOME tv ==>
  encodable_ret_shape tenv (StructT id)
Proof
  strip_tac >> irule (last (CONJUNCTS encodable_ret_shape_rules)) >> simp[]
QED

Theorem encodable_ret_empty_struct_zero_copy:
  FLOOKUP tenv id = SOME (StructArgs []) /\
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent sf tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
     type_memory_bytes cenv t = type_memory_size tv) ==>
  encodable_ret_shape tenv (StructT id) /\
  abi_enc_plan tenv (StructT id) (AbiCopy 0)
Proof
  strip_tac >>
  `evaluate_type tenv (StructT id) = SOME (StructTV [])` by
    simp[evaluate_type_def, type_slot_size_def] >>
  conj_tac >- (irule encodable_ret_shape_empty_struct >> simp[]) >>
  `0 = type_memory_size (StructTV [])` by simp[type_memory_size_def] >>
  pop_assum SUBST1_TAC >> irule abi_enc_plan_copy >>
  simp[vyperABITheory.vyper_to_abi_type_def,
    contractABITheory.is_dynamic_def, contractABITheory.static_length_def,
    type_memory_size_def]
QED
