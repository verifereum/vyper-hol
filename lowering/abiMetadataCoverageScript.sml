(* A consistently erased witness tracks only reachable compiler struct names. *)
Theory abiMetadataCoverage
Ancestors
  abiMetadataErasure abiLayoutSource compileEnv vyperValue vyperTypeABI
  finite_map list pair combin

Definition abi_metadata_coverage_def:
  abi_metadata_coverage sf env ty tv <=>
    ?aux. aux SUBMAP env /\ sfields_tenv_consistent sf aux /\
          evaluate_type aux ty = SOME tv
End

Theorem abi_metadata_coverage_root:
  sfields_tenv_consistent sf env /\ evaluate_type env ty = SOME tv ==>
  abi_metadata_coverage sf env ty tv
Proof
  strip_tac >> simp[abi_metadata_coverage_def] >> qexists_tac `env` >> simp[]
QED

Theorem abi_metadata_coverage_evaluate:
  abi_metadata_coverage sf env ty tv ==> evaluate_type env ty = SOME tv
Proof
  simp[abi_metadata_coverage_def] >> metis_tac[vyper_to_abi_type_submap]
QED

Theorem abi_metadata_coverage_array:
  abi_metadata_coverage sf env (ArrayT ty bound) (ArrayTV tv bound) ==>
  abi_metadata_coverage sf env ty tv
Proof
  simp[abi_metadata_coverage_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >> qexists_tac `aux` >> simp[]
QED

Theorem abi_metadata_coverage_tuple:
  abi_metadata_coverage sf env (TupleT tys) (TupleTV tvs) ==>
  LIST_REL (abi_metadata_coverage sf env) tys tvs
Proof
  simp[abi_metadata_coverage_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >>
  match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac >>
  simp[abi_metadata_coverage_def] >> qexists_tac `aux` >> simp[]
QED

Theorem abi_metadata_coverage_struct:
  abi_metadata_coverage sf env (StructT a) tv ==>
  ?args fields tvs.
    FLOOKUP env a = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string a) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    tv = StructTV (ZIP(MAP FST args,tvs)) /\
    LIST_REL (abi_metadata_coverage (sf \\ nsid_to_string a) (env \\ a))
      (MAP SND args) tvs
Proof
  simp[abi_metadata_coverage_def] >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `FLOOKUP env a = SOME (StructArgs args)` by metis_tac[SUBMAP_FLOOKUP_EQN] >>
  drule_all evaluate_types_erase_struct_aliases >>
  qmatch_goalsub_abbrev_tac `evaluate_types erased _ _` >> strip_tac >>
  `sfields_tenv_consistent (sf \\ nsid_to_string a) erased` by
    (drule sfields_tenv_consistent_erase_aliases >>
     disch_then (qspec_then `a` mp_tac) >> simp[Abbr `erased`]) >>
  `erased SUBMAP env \\ a` by
    (gvs[Abbr `erased`, SUBMAP_FLOOKUP_EQN, FLOOKUP_DRESTRICT,
         DOMSUB_FLOOKUP_THM] >> rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `?fields. FLOOKUP sf (nsid_to_string a) = SOME fields /\
      MAP FST fields = MAP FST args /\
      MAP (FST o SND) fields = MAP SND args` by
    metis_tac[sfields_tenv_consistent_def] >>
  `MAP (\(name,ty,sz). (name,ty)) fields = args` by
    (irule LIST_EQ >>
     `LENGTH fields = LENGTH args` by metis_tac[LENGTH_MAP] >>
     simp[EL_MAP] >> rpt strip_tac >>
     qpat_x_assum `MAP FST fields = _` (mp_tac o Q.AP_TERM `EL x`) >>
     qpat_x_assum `MAP (FST o SND) fields = _` (mp_tac o Q.AP_TERM `EL x`) >>
     simp[EL_MAP] >>
     Cases_on `EL x fields` >> Cases_on `SND (EL x fields)` >>
     Cases_on `EL x args` >> gvs[]) >>
  qexistsl_tac [`fields`, `tvs`] >> simp[] >>
  qpat_x_assum `evaluate_types erased _ _ = _` mp_tac >>
  disch_then (mp_tac o MATCH_MP evaluate_types_LIST_REL) >>
  match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac >>
  simp[abi_metadata_coverage_def] >> qexists_tac `erased` >> simp[]
QED
