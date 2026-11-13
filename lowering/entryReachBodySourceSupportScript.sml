Theory entryReachBodySourceSupport
Ancestors
  entryReachBodyConversionSupport supportedTypes vyperContext vyperTypeABI
  finite_map list pair vyperValue combin

Theorem entry_supported_struct_fields:
  !tops id fields.
  supported_struct_fields tops id = SOME fields <=>
  FLOOKUP (type_env tops) id = SOME (StructArgs fields)
Proof
  Induct_on `tops` >> Cases_on `id` >> Cases_on `q` >>
  simp[type_env_def, type_env_for_module_def, supported_struct_fields_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[type_env_def, type_env_for_module_def, supported_struct_fields_def,
       FLOOKUP_UPDATE] >>
  rpt (IF_CASES_TAC >> gvs[]) >> gvs[type_env_def] >>
  first_x_assum (qspec_then `(SOME x,r)` mp_tac) >>
  simp[supported_struct_fields_other_module]
QED

Theorem entry_supported_nested_evaluated_aux[local]:
  !leaf fuel tops ty env tv.
  leaf = supported_scalar_type /\
  supported_nested_type leaf fuel tops ty /\
  (!id a. FLOOKUP env id = SOME a ==> FLOOKUP (type_env tops) id = SOME a) /\
  evaluate_type env ty = SOME tv ==> entry_abi_support env ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >>
  gvs[] >> Cases_on `supported_scalar_type ty`
  >- metis_tac[entry_abi_support_rules, entry_abi_leaf_scalar] >>
  Cases_on `ty` >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def] >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()]
  >~ [`entry_abi_support env (TupleT tys)`] >-
    (gvs[entry_abi_support_tuple] >>
     drule evaluate_types_LIST_REL >>
     simp[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     first_x_assum irule >> gvs[EVERY_EL, MEM_EL] >>
     qexists_tac `n` >> simp[]) >>
  all_tac
  >~ [`entry_abi_support env (ArrayT elem bd)`] >-
    (Cases_on `bd` >> gvs[entry_abi_support_array] >>
     first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  `FLOOKUP (type_env tops) p = SOME (StructArgs args)` by
    (first_x_assum irule >> simp[]) >>
  `supported_struct_fields tops p = SOME args` by
    simp[entry_supported_struct_fields] >>
  gvs[entry_abi_support_struct] >>
  `!id a. FLOOKUP (env \\ p) id = SOME a ==>
          FLOOKUP (type_env tops) id = SOME a` by
    (simp[DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  drule evaluate_types_LIST_REL >>
  simp[LIST_REL_EL_EQN, EVERY_EL, EL_MAP, o_DEF] >> rpt strip_tac >>
  first_x_assum irule >> gvs[EVERY_EL, MEM_EL, o_DEF] >>
  qexists_tac `n` >> simp[]
QED

Theorem entry_supported_nested_evaluated:
  supported_nested_type supported_scalar_type fuel tops ty /\
  (!id a. FLOOKUP env id = SOME a ==> FLOOKUP (type_env tops) id = SOME a) /\
  evaluate_type env ty = SOME tv ==> entry_abi_support env ty
Proof
  metis_tac[entry_supported_nested_evaluated_aux]
QED

Theorem entry_supported_place_evaluated:
  supported_place_type tops ty /\ evaluate_type (type_env tops) ty = SOME tv ==>
  entry_abi_support (type_env tops) ty
Proof
  strip_tac >> irule entry_supported_nested_evaluated >>
  gvs[supported_place_type_def] >> goal_assum (drule_at Any) >> simp[]
QED
