(* Selected-module type lookup boundaries. Successful lookups, not whole
   maps, are preserved when the source combines all module namespaces. *)
Theory bodyIntCallTypeEval
Ancestors
  vyperContext vyperValue supportedTypes list alist finite_map

Theorem type_env_for_module_other_namespace:
  !tops src other n.
    src <> other ==>
    FLOOKUP (type_env_for_module src tops) (other,n) = NONE
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases_on `h` >> simp[type_env_for_module_def, FLOOKUP_UPDATE]
QED

Theorem selected_module_type_lookup:
  !mods src tops n a.
    ALOOKUP mods src = SOME tops /\
    FLOOKUP (type_env_for_module src tops) (src,n) = SOME a ==>
    FLOOKUP (type_env_all_modules mods) (src,n) = SOME a
Proof
  Induct >- simp[] >> PairCases >> rpt gen_tac >>
  simp[ALOOKUP_def, type_env_all_modules_def] >>
  Cases_on `h0 = src` >> gvs[FLOOKUP_FUNION] >>
  simp[type_env_for_module_other_namespace]
QED

Theorem get_tenv_selected_module_type_lookup:
  get_module_code cx src = SOME tops /\
  FLOOKUP (type_env_for_module src tops) (src,n) = SOME a ==>
  FLOOKUP (get_tenv cx) (src,n) = SOME a
Proof
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  simp[get_module_code_def, get_tenv_def] >>
  strip_tac >> irule selected_module_type_lookup >> metis_tac[]
QED

Theorem supported_scalar_evaluate_type_env_independent:
  !ty env1 env2.
    supported_scalar_type ty ==>
    evaluate_type env1 ty = evaluate_type env2 ty
Proof
  Cases >> simp[supported_scalar_type_def, supported_word_type_def,
                 supported_string_type_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_type_def]
QED

Theorem supported_struct_fields_type_env_lookup:
  !tops id fields.
    supported_struct_fields tops id = SOME fields ==>
    FLOOKUP (type_env tops) id = SOME (StructArgs fields)
Proof
  Induct >- simp[supported_struct_fields_def] >>
  gen_tac >> PairCases >> Cases_on `h` >>
  simp[supported_struct_fields_def, type_env_def,
       type_env_for_module_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[type_env_def] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem supported_scalars_evaluate_types_env_independent:
  !tys env1 env2 acc.
    EVERY supported_scalar_type tys ==>
    evaluate_types env1 tys acc = evaluate_types env2 tys acc
Proof
  Induct >- simp[evaluate_type_def] >>
  rpt strip_tac >> gvs[EVERY_DEF] >>
  drule supported_scalar_evaluate_type_env_independent >>
  disch_then (qspecl_then [`env1`, `env2`] assume_tac) >>
  simp[evaluate_type_def] >>
  Cases_on `evaluate_type env2 h` >> simp[]
QED

Theorem supported_value_evaluate_type_get_tenv:
  supported_value_type tops ty /\ get_module_code cx NONE = SOME tops ==>
  evaluate_type (get_tenv cx) ty = evaluate_type (type_env tops) ty
Proof
  simp[supported_value_type_def] >> strip_tac
  >- metis_tac[supported_scalar_evaluate_type_env_independent] >>
  Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def]
  >~ [`TupleT tys`] >-
    (drule supported_scalars_evaluate_types_env_independent >>
     disch_then (qspecl_then [`get_tenv cx`, `type_env tops`, `[]`] assume_tac) >>
     simp[evaluate_type_def])
  >~ [`ArrayT elem bd`] >-
    (Cases_on `bd` >> gvs[] >>
     `supported_scalar_type elem` by simp[supported_scalar_type_def] >>
     drule supported_scalar_evaluate_type_env_independent >>
     disch_then (qspecl_then [`get_tenv cx`, `type_env tops`] assume_tac) >>
     simp[evaluate_type_def]) >>
  PairCases_on `p` >>
  Cases_on `supported_struct_fields tops (p0,p1)` >> gvs[] >>
  rename1 `supported_struct_fields tops (p0,p1) = SOME fields` >>
  `p0 = NONE` by
    (Cases_on `p0 = NONE` >>
     gvs[supported_struct_fields_other_module]) >> gvs[] >>
  drule supported_struct_fields_type_env_lookup >> strip_tac >>
  `FLOOKUP (get_tenv cx) (NONE,p1) = SOME (StructArgs fields)` by
    (irule get_tenv_selected_module_type_lookup >>
     gvs[type_env_def]) >>
  `EVERY supported_scalar_type (MAP SND fields)` by
    (gvs[EVERY_MAP, EVERY_MEM, supported_scalar_type_def] >>
     metis_tac[]) >>
  drule supported_scalars_evaluate_types_env_independent >>
  disch_then (qspecl_then [`get_tenv cx \\ (NONE,p1)`,
                           `type_env tops \\ (NONE,p1)`, `[]`] assume_tac) >>
  simp[evaluate_type_def]
QED
