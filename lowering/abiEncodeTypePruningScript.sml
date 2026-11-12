Theory abiEncodeTypePruning
Ancestors
  loweringStateRelDefs
    retAbiPlanProps vyperTyping compileEnv vyperValue finite_map list

Theorem abi_encode_struct_alias_value:
  sfields_tenv_consistent sf tenv /\ nsid_to_string a = nsid_to_string b /\
  evaluate_type tenv (StructT a) = SOME va /\
  evaluate_type tenv (StructT b) = SOME vb ==> va = vb
Proof
  strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `MAP FST args = MAP FST args' /\ MAP SND args = MAP SND args'` by
    (gvs[sfields_tenv_consistent_def] >>
     qpat_assum `!nsid args. FLOOKUP tenv nsid = SOME (StructArgs args) ==> _`
       (qspecl_then [`a`, `args`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
     qpat_x_assum `!nsid args. FLOOKUP tenv nsid = SOME (StructArgs args) ==> _`
       (qspecl_then [`b`, `args'`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >> gvs[]) >>
  `tenv \\ a SUBMAP tenv /\ tenv \\ b SUBMAP tenv` by
    simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyper_to_abi_type_submap] >>
  `evaluate_types tenv (MAP SND args') [] = SOME tvs'` by
    metis_tac[cj 2 vyper_to_abi_type_submap] >>
  gvs[]
QED

Theorem abi_encode_evaluate_types_member:
  evaluate_types env ts [] = SOME tvs /\ MEM t ts ==>
  ?tv. MEM tv tvs /\ evaluate_type env t = SOME tv
Proof
  strip_tac >> drule vyperTypeABITheory.evaluate_types_LIST_REL >>
  disch_then assume_tac >> drule_all LIST_REL_MEM_IMP >> simp[]
QED

Theorem abi_encode_evaluate_types_prune:
  (!env ty tv. evaluate_type env ty = SOME tv ==>
    !E B n. env SUBMAP E /\ type_value_size tv < n /\
      (!k. k IN B ==> ?args. FLOOKUP E k = SOME (StructArgs args)) /\
      (!k w. k IN B /\ evaluate_type E (StructT k) = SOME w ==>
        n <= type_value_size w) ==>
    evaluate_type (DRESTRICT env (COMPL B)) ty = SOME tv) /\
  (!env ts acc tvs. evaluate_types env ts acc = SOME tvs ==>
    !E B n. env SUBMAP E /\ EVERY (\tv. type_value_size tv < n) tvs /\
      (!k. k IN B ==> ?args. FLOOKUP E k = SOME (StructArgs args)) /\
      (!k w. k IN B /\ evaluate_type E (StructT k) = SOME w ==>
        n <= type_value_size w) ==>
    evaluate_types (DRESTRICT env (COMPL B)) ts acc = SOME tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`BaseT bt`] >- simp[evaluate_type_def]
  >~ [`NoneT`] >- simp[evaluate_type_def]
  >~ [`evaluate_types env [] acc`] >- simp[evaluate_type_def]
  >~ [`TupleT ts`]
  >- (rpt strip_tac >>
      qpat_x_assum `evaluate_type env _ = SOME tv` mp_tac >>
      simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `EVERY (\v. type_value_size v < n) tvs` by
        (gvs[EVERY_MEM] >> rpt strip_tac >>
         drule MEM_type_value_size_TupleTV >> simp[type_value_size_def]) >>
      first_x_assum drule >> disch_then drule_all >>
      simp[Once evaluate_type_def])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >>
      qpat_x_assum `evaluate_type env _ = SOME tv` mp_tac >>
      simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `type_value_size tv' < n` by
        (gvs[type_value_size_def] >> decide_tac) >>
      first_x_assum drule >> disch_then drule_all >>
      simp[Once evaluate_type_def])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >>
      qpat_x_assum `evaluate_type env _ = SOME tv` mp_tac >>
      simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `nsid NOTIN B` by
        (strip_tac >>
         qpat_x_assum `!k. k IN B ==> _` drule >> strip_tac >>
         qpat_x_assum `env SUBMAP E` mp_tac >>
         rewrite_tac[SUBMAP_FLOOKUP_EQN] >>
         disch_then drule >> simp[]) >>
      simp[evaluate_type_def, FLOOKUP_DRESTRICT])
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      `evaluate_type E (StructT nsid) = SOME tv` by
        metis_tac[cj 1 vyper_to_abi_type_submap] >>
      `nsid NOTIN B` by
        (strip_tac >> qpat_x_assum `!k w. _` drule_all >> simp[]) >>
      qpat_x_assum `evaluate_type env _ = SOME tv` mp_tac >>
      simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `LENGTH tvs = LENGTH args` by
        (drule vyperTypeDefaultsTheory.evaluate_types_length >> simp[]) >>
      `EVERY (\v. type_value_size v < n) tvs` by
        (rewrite_tac[EVERY_MEM] >> qx_gen_tac `v` >> strip_tac >>
         `?nm. MEM (nm,v) (ZIP (MAP FST args,tvs))` by
           metis_tac[MEM_ZIP, MEM_EL, LENGTH_MAP] >>
         drule MEM_type_value_size_StructTV >> simp[type_value_size_def]) >>
      `env \\ nsid SUBMAP E` by
        gvs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      `DRESTRICT (env \\ nsid) (COMPL B) =
       (DRESTRICT env (COMPL B)) \\ nsid` by
        (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
         gen_tac >> Cases_on `nsid = x` >> simp[]) >>
      first_x_assum drule_all >>
      simp[Once evaluate_type_def, FLOOKUP_DRESTRICT])
  >> rpt strip_tac >>
  qpat_x_assum `evaluate_types env (_::_) acc = SOME tvs` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  `MEM tv tvs` by
    (qpat_assum `evaluate_types env ts (tv::acc) = SOME tvs` mp_tac >>
     pure_rewrite_tac[evaluate_types_OPT_MMAP] >>
     Cases_on `OPT_MMAP (evaluate_type env) ts` >> simp[] >>
     strip_tac >> gvs[]) >>
  `type_value_size tv < n` by gvs[EVERY_MEM] >>
  `evaluate_type (DRESTRICT env (COMPL B)) ty = SOME tv` by
    (qpat_x_assum `!tv. evaluate_type env ty = SOME tv ==> !E B n. _`
       drule_all >> simp[]) >>
  `evaluate_types (DRESTRICT env (COMPL B)) ts (tv::acc) = SOME tvs` by
    (qpat_x_assum `!tv. evaluate_type env ty = SOME tv ==> !tvs. evaluate_types env ts (tv::acc) = SOME tvs ==> _`
       (qspec_then `tv` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`E`, `B`, `n`] mp_tac) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  simp[Once evaluate_type_def]
QED

Theorem abi_encode_alias_restrict_submap:
  DRESTRICT E (COMPL {k | ?fs. FLOOKUP E k = SOME (StructArgs fs) /\
    nsid_to_string k = nsid_to_string a}) SUBMAP E
Proof
  simp[SUBMAP_FLOOKUP_EQN, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem abi_encode_alias_restrict_consistent:
  sfields_tenv_consistent sf E ==>
  sfields_tenv_consistent (sf \\ nsid_to_string a)
    (DRESTRICT E (COMPL {k | ?fs. FLOOKUP E k = SOME (StructArgs fs) /\
      nsid_to_string k = nsid_to_string a}))
Proof
  simp[sfields_tenv_consistent_def, FLOOKUP_DRESTRICT,
    DOMSUB_FLOOKUP_THM] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_encode_alias_restrict_fields:
  sfields_tenv_consistent sf E /\ FLOOKUP E a = SOME (StructArgs args) /\
  evaluate_type E (StructT a) = SOME v /\
  evaluate_types (E \\ a) (MAP SND args) [] = SOME tvs ==>
  evaluate_types
    (DRESTRICT E (COMPL {k | ?fs. FLOOKUP E k = SOME (StructArgs fs) /\
      nsid_to_string k = nsid_to_string a}))
    (MAP SND args) [] = SOME tvs
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type E (StructT a) = SOME v` mp_tac >>
  simp[Once evaluate_type_def] >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `DRESTRICT E (COMPL B)` >>
  `DRESTRICT (E \\ a) (COMPL B) = DRESTRICT E (COMPL B)` by
    (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
     qx_gen_tac `k` >> Cases_on `a = k` >>
     gvs[Abbr `B`]) >>
  `LENGTH tvs = LENGTH args` by
    (drule vyperTypeDefaultsTheory.evaluate_types_length >> simp[]) >>
  `EVERY (\tv. type_value_size tv <
      type_value_size (StructTV (ZIP (MAP FST args,tvs)))) tvs` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `tv` >> strip_tac >>
     `?nm. MEM (nm,tv) (ZIP (MAP FST args,tvs))` by
       metis_tac[MEM_ZIP, MEM_EL, LENGTH_MAP] >>
     metis_tac[MEM_type_value_size_StructTV]) >>
  drule (cj 2 abi_encode_evaluate_types_prune) >>
  disch_then (qspecl_then [`E`, `B`,
    `type_value_size (StructTV (ZIP (MAP FST args,tvs)))`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac
     >- simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM]
     >- simp[]
     >- (gvs[Abbr `B`] >> metis_tac[]) >>
     rpt strip_tac >>
     `evaluate_type E (StructT a) =
        SOME (StructTV (ZIP (MAP FST args,tvs)))` by
       simp[Once evaluate_type_def] >>
     `w = StructTV (ZIP (MAP FST args,tvs))` by
       (irule abi_encode_struct_alias_value >>
        gvs[Abbr `B`] >> metis_tac[]) >> simp[])) >> simp[]
QED
