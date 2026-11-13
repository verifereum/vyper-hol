(* Compiler ABI plans for evaluated structural supported places. *)
Theory supportedPlaceAbiPlan
Ancestors
  retAbiPlanProps supportedTypes abiEncoderProps exprLowering compileEnv loweringStateRelDefs
  vyperTyping vyperTypeSystem vyperTypeValues vyperValue vyperABI
  finite_map list rich_list arithmetic

Theorem supported_nested_type_abi_plan:
  !leaf fuel tops ty.
    leaf = supported_scalar_type ==>
    !tenv tv sf cenv.
    supported_nested_type leaf fuel tops ty /\
    evaluate_type tenv ty = SOME tv /\ tenv SUBMAP type_env tops /\
    sfields_tenv_consistent sf tenv /\
    (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
    sfields_tenv_consistent cenv.ce_struct_fields (type_env tops) /\
    (!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type (type_env tops) t = SOME tv ==>
       type_memory_bytes cenv t = type_memory_size tv) ==>
    abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `supported_scalar_type ty`
  >- (`assignable_type tenv ty` by
        (irule supported_scalar_type_assignable >>
         simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
      drule type_to_abi_enc_info_plan >> disch_then irule >> simp[] >>
      qexists_tac `type_env tops` >> simp[]) >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  Cases_on `ty` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac
  >~ [`abi_enc_plan _ (TupleT _) _`] >- suspend "tuple"
  >~ [`abi_enc_plan _ (ArrayT _ _) _`] >- suspend "array"
  >> suspend "struct"
QED

Resume supported_nested_type_abi_plan[array]:
  Cases_on `b` >> gvs[] >>
  `?etv. evaluate_type tenv t = SOME etv` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `abi_enc_plan tenv t (type_to_abi_enc_info sf cenv t)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC
      >- (irule abi_enc_plan_static_copy >> simp[] >>
          qexists_tac `type_env tops` >> simp[] >> metis_tac[]) >>
      drule_all abi_elem_props >> strip_tac >>
      simp[GSYM REPLICATE_GENLIST] >>
      drule_all abi_enc_plans_replicate >>
      disch_then (qspec_then `n` assume_tac) >>
      irule abi_enc_plan_sarray >> gvs[is_abi_dynamic_def])
  >> drule_all abi_elem_props >> strip_tac >> simp[] >>
  irule abi_enc_plan_dynarray >> simp[]
QED

Resume supported_nested_type_abi_plan[tuple]:
  gvs[] >>
  `!t. MEM t l ==> IS_SOME (evaluate_type tenv t)` by
    (qpat_x_assum `evaluate_type tenv (TupleT _) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP,
          vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_MEM]) >>
  simp[Once type_to_abi_enc_info_def] >>
  IF_CASES_TAC
  >- (irule abi_enc_plan_static_copy >> simp[] >>
      qexists_tac `type_env tops` >> simp[] >> metis_tac[]) >>
  drule_all abi_elem_props >> strip_tac >>
  irule abi_enc_plan_tuple >>
  conj_tac >- fs[vyper_to_abi_type_def, contractABITheory.is_dynamic_def] >>
  irule abi_enc_plans_map >> simp[] >>
  reverse conj_tac >- (qexists_tac `type_env tops` >> simp[]) >>
  rpt strip_tac >> simp[] >>
  first_x_assum irule >> simp[] >>
  fs[EVERY_MEM, optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Resume supported_nested_type_abi_plan[struct]:
  gvs[] >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  rename1 `supported_struct_fields tops p = SOME args` >>
  drule supported_struct_fields_type_env >> strip_tac >>
  `FLOOKUP tenv p = SOME (StructArgs args)` by
    (qpat_x_assum `evaluate_type tenv (StructT _) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
     qpat_x_assum `tenv SUBMAP _`
       (mp_tac o REWRITE_RULE [SUBMAP_FLOOKUP_EQN]) >>
     disch_then drule >> simp[]) >>
  simp[Once type_to_abi_enc_info_def] >> IF_CASES_TAC
  >- (irule abi_enc_plan_static_copy >> simp[] >>
      qexists_tac `type_env tops` >> simp[] >> metis_tac[]) >>
  `?fields. FLOOKUP sf (nsid_to_string p) = SOME fields /\
     MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `sfields_tenv_consistent sf tenv` mp_tac >>
     simp[sfields_tenv_consistent_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> simp[]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `MAP f fields` >>
  `MAP f fields = MAP (\t. (type_to_abi_enc_info (sf \\ nsid_to_string p) cenv t,
      abi_embedded_static_size cenv.ce_struct_fields t, type_memory_bytes cenv t,
      is_abi_dynamic cenv.ce_struct_fields t)) (MAP SND args)` by
    (qpat_x_assum `MAP (FST o SND) fields = _` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD, Abbr `f`]) >>
  simp[] >>
  drule_all abi_elem_props >> strip_tac >>
  irule abi_enc_plan_struct >>
  conj_tac >- gvs[contractABITheory.is_dynamic_def] >>
  qexists_tac `args` >> simp[] >> suspend "struct_children"
QED

Resume supported_nested_type_abi_plan[struct_children]:
  qpat_x_assum `FLOOKUP (type_env tops) p = _` kall_tac >>
  drule_all sfields_tenv_consistent_domsub >> strip_tac >>
  `tenv \\ p SUBMAP type_env tops` by
    (irule SUBMAP_TRANS >> qexists_tac `tenv` >> simp[]) >>
  `!t. MEM t (MAP SND args) ==> IS_SOME (evaluate_type (tenv \\ p) t)` by
    (qpat_x_assum `evaluate_type tenv (StructT _) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP,
          vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_MEM,
          MEM_MAP, PULL_EXISTS]) >>
  irule abi_enc_plans_map >> simp[] >>
  reverse conj_tac >- (qexists_tac `type_env tops` >> simp[]) >>
  simp[MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `!x. MEM x args ==> _` drule >>
  disch_then irule >> simp[] >>
  fs[EVERY_MEM, optionTheory.IS_SOME_EXISTS] >> metis_tac[MEM_MAP]
QED

Finalise supported_nested_type_abi_plan

Theorem supported_place_type_abi_plan:
  supported_place_type tops ty /\
  evaluate_type (type_env tops) ty = SOME tv /\
  sfields_tenv_consistent cenv.ce_struct_fields (type_env tops) /\
  (!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type (type_env tops) t = SOME tv ==>
     type_memory_bytes cenv t = type_memory_size tv) ==>
  abi_enc_plan (type_env tops) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)
Proof
  strip_tac >> irule supported_nested_type_abi_plan >>
  simp[] >> qexistsl_tac [`LENGTH tops`, `tops`] >>
  gvs[supported_place_type_def]
QED
