Theory abiMetadataErasure
Ancestors
  retAbiPlanProps compileEnv vyperTypeABI vyperValue vyperAST finite_map list rich_list

Theorem evaluate_types_acc_every[local]:
  evaluate_types env ts acc = SOME out /\ EVERY P out ==> EVERY P acc
Proof
  strip_tac >> gvs[evaluate_types_OPT_MMAP, AllCaseEqs(),
                   EVERY_APPEND, EVERY_REVERSE]
QED

Theorem type_value_list_size_bound[local]:
  !xs n. list_size type_value_size xs < n ==>
    EVERY (\tv. type_value_size tv < n) xs
Proof
  Induct >> simp[] >> rpt strip_tac >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem type_value_zip_size_bound[local]:
  !names tvs n. LENGTH names = LENGTH tvs /\
    type_value_size (StructTV (ZIP(names,tvs))) <= n ==>
    EVERY (\tv. type_value_size tv < n) tvs
Proof
  Induct >> Cases_on `tvs` >>
  simp[vyperValueTheory.type_value_size_def]
QED

(* A forbidden declaration cannot occur below its own evaluated size. *)
Theorem evaluate_type_restrict_small[local]:
  (!env ty tv. evaluate_type env ty = SOME tv ==>
    !root bad n.
      env SUBMAP root /\ type_value_size tv < n /\
      (!k. k IN bad ==> ?args. FLOOKUP root k = SOME (StructArgs args)) /\
      (!k args vs. k IN bad /\ FLOOKUP root k = SOME (StructArgs args) /\
         evaluate_types root (MAP SND args) [] = SOME vs ==>
         n <= type_value_size (StructTV (ZIP(MAP FST args,vs)))) ==>
      evaluate_type (DRESTRICT env (COMPL bad)) ty = SOME tv) /\
  (!env ts acc out. evaluate_types env ts acc = SOME out ==>
    !root bad n.
      env SUBMAP root /\ EVERY (\tv. type_value_size tv < n) out /\
      (!k. k IN bad ==> ?args. FLOOKUP root k = SOME (StructArgs args)) /\
      (!k args vs. k IN bad /\ FLOOKUP root k = SOME (StructArgs args) /\
         evaluate_types root (MAP SND args) [] = SOME vs ==>
         n <= type_value_size (StructTV (ZIP(MAP FST args,vs)))) ==>
      evaluate_types (DRESTRICT env (COMPL bad)) ts acc = SOME out)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      `env \\ nsid SUBMAP root`
        by (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
      `evaluate_types root (MAP SND args) [] = SOME tvs`
        by metis_tac[vyper_to_abi_type_submap] >>
      `~(nsid IN bad)` by
        (strip_tac >>
         `FLOOKUP root nsid = SOME (StructArgs args)`
           by metis_tac[SUBMAP_FLOOKUP_EQN] >>
         first_x_assum drule_all >> simp[]) >>
      `LENGTH tvs = LENGTH args`
        by (drule evaluate_types_LIST_REL >>
            disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
      `EVERY (\tv. type_value_size tv < n) tvs`
        by (irule type_value_zip_size_bound >> qexists_tac `MAP FST args` >>
            simp[type_value_size_def]) >>
      simp[FLOOKUP_DRESTRICT, GSYM DRESTRICT_DOMSUB] >>
      qexists_tac `tvs` >> simp[] >>
      `DRESTRICT env (COMPL bad) \\ nsid =
       DRESTRICT (env \\ nsid) (COMPL bad)`
        by (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
            gen_tac >> IF_CASES_TAC >> simp[]) >>
      asm_rewrite_tac[] >>
      first_x_assum irule >> qexistsl_tac [`n`, `root`] >> simp[] >> first_assum ACCEPT_TAC)
  >~ [`BaseT bt`] >- (simp[evaluate_type_def])
  >~ [`NoneT`] >- simp[evaluate_type_def]
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      `~(nsid IN bad)` by
        (strip_tac >>
         `FLOOKUP root nsid = SOME (FlagArgs m)`
           by metis_tac[SUBMAP_FLOOKUP_EQN] >>
         metis_tac[type_args_distinct, optionTheory.SOME_11]) >>
      simp[FLOOKUP_DRESTRICT])
  >~ [`TupleT ts`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      `EVERY (\tv. type_value_size tv < n) tvs`
        by (irule type_value_list_size_bound >> gvs[type_value_size_def]) >>
      `evaluate_types (DRESTRICT env (COMPL bad)) ts [] = SOME tvs`
        by (first_x_assum irule >>
            qexistsl_tac [`n`, `root`] >> simp[] >> first_assum ACCEPT_TAC) >>
      simp[])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum irule >> qexistsl_tac [`n`, `root`] >>
      simp[] >> first_assum ACCEPT_TAC)
  >> rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_value_size tv < n`
    by (drule_all evaluate_types_acc_every >> simp[]) >>
  qexists_tac `tv` >> conj_tac >>
  first_x_assum irule >> qexistsl_tac [`n`, `root`] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem evaluate_types_erase_equal_declarations:
  evaluate_types env (MAP SND args) [] = SOME tvs /\ env SUBMAP root /\
  (!k. k IN bad ==> FLOOKUP root k = SOME (StructArgs args)) ==>
  evaluate_types (DRESTRICT env (COMPL bad)) (MAP SND args) [] = SOME tvs
Proof
  strip_tac >>
  `evaluate_types root (MAP SND args) [] = SOME tvs`
    by metis_tac[vyper_to_abi_type_submap] >>
  `LENGTH tvs = LENGTH args`
    by (drule evaluate_types_LIST_REL >>
        disch_then (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
  irule (cj 2 evaluate_type_restrict_small) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`type_value_size (StructTV (ZIP(MAP FST args,tvs)))`, `root`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >> irule type_value_zip_size_bound >> qexists_tac `MAP FST args` >> simp[]
QED

Theorem evaluate_types_erase_struct_aliases:
  sfields_tenv_consistent sf root /\
  FLOOKUP root a = SOME (StructArgs args) /\
  evaluate_types (root \\ a) (MAP SND args) [] = SOME tvs ==>
  evaluate_types
    (DRESTRICT root {k | nsid_to_string k <> nsid_to_string a \/
                       (!xs. FLOOKUP root k <> SOME (StructArgs xs))})
    (MAP SND args) [] = SOME tvs
Proof
  strip_tac >>
  qabbrev_tac `bad = {k | nsid_to_string k = nsid_to_string a /\
                              ?xs. FLOOKUP root k = SOME (StructArgs xs)}` >>
  `!k. k IN bad ==> FLOOKUP root k = SOME (StructArgs args)` by
    (gvs[Abbr `bad`, sfields_tenv_consistent_def] >> rpt strip_tac >>
     qpat_assum `!nsid args. _` (qspecl_then [`a`, `args`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `!nsid args. _` (qspecl_then [`k`, `xs`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     gvs[] >> metis_tac[UNZIP_MAP, ZIP_UNZIP]) >>
  `evaluate_types (DRESTRICT (root \\ a) (COMPL bad))
       (MAP SND args) [] = SOME tvs` by
    (irule evaluate_types_erase_equal_declarations >> simp[] >>
     qexists_tac `root` >> simp[]) >>
  `DRESTRICT (root \\ a) (COMPL bad) SUBMAP DRESTRICT root (COMPL bad)`
    by (simp[SUBMAP_FLOOKUP_EQN, FLOOKUP_DRESTRICT, DOMSUB_FLOOKUP_THM] >>
        rpt strip_tac >> gvs[AllCaseEqs()]) >>
  drule (cj 2 vyper_to_abi_type_submap) >>
  disch_then drule >>
  simp[Abbr `bad`, pred_setTheory.COMPL_DEF, pred_setTheory.DIFF_DEF]
QED
