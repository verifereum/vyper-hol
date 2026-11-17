(* Structural label distinctness boundary. These statements and proofs
   are relocated verbatim from externalEntryChecks, which imports this
   slim theory instead of defining duplicate copies. *)
Theory classifiedExternalLabels
Ancestors entryDispatchProps loweringShapeProps compileVyper vyperTypeContract
  loweringShapeSource list pair

Theorem raw_external_name_key[local]:
  !tops name.
    MEM name (MAP (\p. FST (SND (SND (SND p))))
      (FST (FOLDR classify_function ([],[],NONE,NONE) tops) ++
       public_getters tops)) ==>
    MEM (NONE:num option,name)
      (FLAT (MAP (external_name_keys_toplevel NONE) tops))
Proof
  simp[MAP_APPEND, MEM_MAP, EXISTS_PROD] >> rpt strip_tac
  >- (drule loweringShapePropsTheory.classify_fold_external_source >>
      strip_tac >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      goal_assum (drule_at Any) >> simp[vyperTypeContractTheory.external_name_keys_toplevel_def]) >>
  gvs[MEM_public_getters] >>
  drule public_getter_lookup_singleton >> strip_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_external_names_distinct[local]:
  !tops.
    ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) ==>
    ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
      (FST (FOLDR classify_function ([],[],NONE,NONE) tops) ++ public_getters tops))
Proof
  Induct >- simp[public_getters_def] >>
  gen_tac >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `r` >>
  Cases_on `h` >>
  gvs[classify_function_def, public_getters_def,
      vyperTypeContractTheory.external_name_keys_toplevel_def]
  >~ [`FunctionDecl vis`] >- (
    Cases_on `vis` >>
    simp[public_getter_def, vyperTypeContractTheory.external_name_keys_toplevel_def] >>
    rpt strip_tac >> gvs[] >>
    Cases_on `s = "__default__"` >> gvs[] >>
    metis_tac[raw_external_name_key, MAP_APPEND, MEM_APPEND, FST])
  >~ [`VariableDecl kind`] >- (
    Cases_on `kind` >>
    gvs[public_getter_def, vyperTypeContractTheory.external_name_keys_toplevel_def] >>
    Cases_on `is_ArrayT t` >> gvs[]
    >- (pairarg_tac >> gvs[] >> rpt strip_tac >>
        qspecl_then [`tops`, `s`] mp_tac raw_external_name_key >>
        gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    rpt strip_tac >>
    qspecl_then [`tops`, `s`] mp_tac raw_external_name_key >>
    gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >~ [`HashMapDecl kind`] >- (
    Cases_on `kind` >>
    gvs[public_getter_def, vyperTypeContractTheory.external_name_keys_toplevel_def] >>
    pairarg_tac >> gvs[] >> rpt strip_tac >>
    qspecl_then [`tops`, `s`] mp_tac raw_external_name_key >>
    gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  simp[public_getter_def]
QED

Theorem classified_external_labels_distinct:
  !tops.
    ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) ==>
    ALL_DISTINCT (MAP (\(mut,nr,rr,name,args,dflts,ret,fbody). "fn_" ++ name)
      (FST (classify_functions tops)))
Proof
  gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
     (FST (classify_functions tops)))` by
    (Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
     PairCases_on `r` >>
     simp[classify_functions_def, loweringShapeSourceTheory.subst_consts_fn_names] >>
     drule raw_external_names_distinct >> simp[]) >>
  `MAP (\(mut,nr,rr,name,args,dflts,ret,fbody). "fn_" ++ name)
      (FST (classify_functions tops)) =
   MAP (\name. "fn_" ++ name)
     (MAP (\p. FST (SND (SND (SND p))))
       (FST (classify_functions tops)))` by
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  pop_assum SUBST1_TAC >>
  irule ALL_DISTINCT_MAP_INJ >> simp[]
QED
