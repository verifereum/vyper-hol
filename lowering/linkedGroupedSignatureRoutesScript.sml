Theory linkedGroupedSignatureRoutes
Ancestors
  dispatchedSignatureOriginMods dispatchedClassifierMods defaultDispatchModsGetter
  checkedSelectorTableProps e2eModsDefs compileUnit compileVyper constSubstMods
  publicGetterProps vyperABIEntries vyperTypeContract vyperReadOnlySyntax alist list pair

val _ = Parse.hide "body";

Theorem deployed_grouped_signature_member_mods:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  MEM (name,tys) (abi_deployed_signatures mods exps) ==>
  ?tops top mut nr rr args dflts ret body prefix k.
    ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
    ((name <> "__default__" /\
      top = FunctionDecl External mut nr rr name args dflts ret body) \/
     public_getter_src (ALOOKUP exps name) top =
       SOME (mut,nr,rr,name,args,dflts,ret,body)) /\
    abi_decl_signatures top = abi_function_signatures name args dflts /\
    MEM (prefix,k) (abi_entries args dflts) /\ tys = MAP SND prefix /\
    MEM (ALOOKUP exps name,
      subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,ret,body)) exts
Proof
  strip_tac >>
  drule_all (SRULE [LET_THM] deployed_signature_selected_module) >>
  strip_tac >>
  rename1 `MEM (name,tys) (abi_decl_signatures top)` >>
  rename1 `ALOOKUP mods (ALOOKUP exps name) = SOME src_tops` >>
  (Q.SUBGOAL_THEN `?mut nr rr args dflts ret rawbody.
     (name <> "__default__" /\
      top = FunctionDecl External mut nr rr name args dflts ret rawbody) \/
     public_getter_src (ALOOKUP exps name) top =
       SOME (mut,nr,rr,name,args,dflts,ret,rawbody)`
     (qx_choosel_then [`mut`,`nr`,`rr`,`args`,`dflts`,`ret`,`rawbody`] assume_tac)
   >- (qpat_x_assum `MEM (name,tys) (abi_decl_signatures top)` mp_tac >>
     Cases_on `top` >> simp[abi_decl_signatures_def]
     >- (Cases_on `f` >> simp[abi_decl_signatures_def] >>
         IF_CASES_TAC >> simp[abi_function_signatures_def, MEM_MAP, EXISTS_PROD] >>
         strip_tac >> gvs[] >> metis_tac[])
     >- (Cases_on `v` >> simp[abi_decl_signatures_def, public_getter_src_def] >>
         rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[]) >>
     Cases_on `v` >> simp[abi_decl_signatures_def, public_getter_src_def] >>
     rpt strip_tac >> gvs[] >> pairarg_tac >> simp[])) >>
  `abi_decl_signatures top = abi_function_signatures name args dflts` by
    (qpat_assum `(name <> "__default__" /\ _) \/ _` strip_assume_tac
     >- gvs[abi_decl_signatures_def] >>
     drule tagged_getter_decl_signature >> simp[abi_function_signatures_def] >>
     fs[tagged_getter_source_tuple] >>
     drule external_getter_defaults >> simp[abi_entries_no_defaults]) >>
  drule_all_then assume_tac selected_external_member_with_defaults_mods >>
  qpat_x_assum `MEM (name,tys) (abi_decl_signatures top)` mp_tac >>
  qpat_assum `abi_decl_signatures top = _` (fn eq =>
    simp[NoAsms, eq, abi_function_signatures_def, MEM_MAP, EXISTS_PROD]) >>
  disch_then (qx_choosel_then [`pref`,`k`] strip_assume_tac) >>
  qexistsl_tac [`src_tops`,`top`,`mut`,`nr`,`rr`,`args`,`dflts`,`ret`,`rawbody`,`pref`,`k`] >>
  asm_rewrite_tac[abi_function_signatures_def]
QED

Theorem classified_grouped_member_signature_mods:
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  MEM (src,(mut,nr,rr,name,args,ds,ret,code)) exts /\
  MEM (pref,k) (abi_entries args ds) ==>
  MEM (name,MAP SND pref) (abi_deployed_signatures mods exps)
Proof
  strip_tac >>
  `!tops mut nr rr name args ds ret body pref k.
     MEM (mut,nr,rr,name,args,ds,ret,body)
       (FST (FOLDR classify_function ([],[],NONE,NONE) tops)) /\
     MEM (pref,k) (abi_entries args ds) ==>
     MEM (name,MAP SND pref) (abi_external_signatures tops)` by
    (rpt (pop_assum kall_tac) >> Induct >> simp[abi_external_signatures_def] >>
     qx_gen_tac `top` >> simp[checkedSelectorTablePropsTheory.classify_function_external_component] >>
     Cases_on `top` >> simp[] >> BasicProvers.every_case_tac >> gvs[] >> rpt strip_tac >>
     gvs[abi_decl_signatures_def, abi_function_signatures_def, MEM_MAP, EXISTS_PROD] >>
     metis_tac[abi_external_signatures_def]) >>
  `!tag src tops key mut nr rr name args ds ret body pref k.
     MEM (tag,(mut,nr,rr,name,args,ds,ret,body)) (exported_fn src tops key) /\
     MEM (pref,k) (abi_entries args ds) ==>
     name = key /\ MEM (name,MAP SND pref) (abi_external_signatures tops)` by
    (qpat_x_assum `!tops mut nr rr name args ds ret body pref k. _` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     rpt gen_tac >> simp[exported_fn_def] >> pairarg_tac >> gvs[] >>
     rename1 `FOLDR classify_function _ ts = (raw,_,_,_)` >>
     Cases_on `FILTER (\f. fn_decl_name f = key) raw` >> gvs[]
     >- (Cases_on `FILTER (\g. fn_decl_name g = key)
          (FLAT (MAP (\t. case public_getter_src src t of
                            NONE => [] | SOME g => [g]) ts))` >> gvs[] >>
         strip_tac >> gvs[] >>
         rename1 `FILTER _ _ = (mut,nr,rr,name,args,ds,ret,fbody)::_` >>
         qpat_assum `FILTER _ _ = _ :: _`
           (mp_tac o Q.AP_TERM `MEM (mut,nr,rr,name,args,ds,ret,fbody)`) >>
         simp[MEM_FILTER, fn_decl_name_def, MEM_FLAT, MEM_MAP, AllCaseEqs()] >>
         strip_tac >> gvs[] >>
         rename1 `public_getter_src src top = SOME _` >>
         drule tagged_getter_decl_signature >> strip_tac >>
         qpat_assum `public_getter_src src top = SOME _`
           (strip_assume_tac o REWRITE_RULE [tagged_getter_source_tuple]) >>
         drule_then assume_tac external_getter_defaults >>
         gvs[abi_entries_no_defaults] >>
         simp[abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
         qexists_tac `abi_decl_signatures top` >>
         conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]) >>
     strip_tac >> gvs[] >>
     rename1 `FILTER _ _ = (mut,nr,rr,name,args,ds,ret,fbody)::_` >>
     qpat_assum `FILTER _ _ = _ :: _`
       (mp_tac o Q.AP_TERM `MEM (mut,nr,rr,name,args,ds,ret,fbody)`) >>
     simp[MEM_FILTER, fn_decl_name_def] >>
     strip_tac >> gvs[] >>
     qpat_assum `!tops mut nr rr name args ds ret body pref k. _`
       (qspecl_then [`ts`,`mut`,`nr`,`rr`,`key`,`args`,`ds`,`ret`,`fbody`,`pref`,`k`] mp_tac) >>
     simp[]) >>
  `!exports src mut nr rr name args ds ret body pref k.
     MEM (src,(mut,nr,rr,name,args,ds,ret,body)) (exported_fns mods exports) /\
     MEM (pref,k) (abi_entries args ds) ==>
     MEM (name,MAP SND pref)
       (FLAT (MAP (\(key,owner). case ALOOKUP mods (SOME owner) of
          NONE => [] | SOME declarations => FILTER (\(nm,tys). nm = key)
            (abi_external_signatures declarations)) exports))` by
    (qpat_x_assum `!tag src tops key mut nr rr name args ds ret body pref k. _` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     Induct >> simp[exported_fns_def] >> qx_gen_tac `exp` >> PairCases_on `exp` >>
     simp[exported_fns_def] >> rpt gen_tac >>
     Cases_on `ALOOKUP mods (SOME exp1)` >> simp[MEM_FILTER] >>
     rpt strip_tac >>
     (qpat_assum `!src mut nr rr name args ds ret body pref k. _` drule_all >> simp[] >> NO_TAC
      ORELSE
      qpat_assum `!tag src tops key mut nr rr name args ds ret body pref k. _` drule_all >> simp[])) >>
  `!es. LENGTH (subst_consts_exprs_mods (consts_env_mods mods) es) = LENGTH es` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  qpat_assum `classify_functions_unit mods exps = _` mp_tac >>
  simp[NoAsms, classify_functions_unit_def] >> pairarg_tac >>
  first_assum (fn th => simp[NoAsms,th]) >>
  disch_then (assume_tac o SYM o CONJUNCT1) >>
  qpat_x_assum `MEM (src,(mut,nr,rr,name,args,ds,ret,code)) exts` mp_tac >>
  qpat_assum `exts = _ ++ _` (fn selected =>
    simp[NoAsms, selected, MEM_MAP, MEM_APPEND, EXISTS_PROD, MAP_MAP_o, combinTheory.o_DEF]) >>
  strip_tac >>
  rename1 `_ = subst_consts_fn_mods _ (_,_,_,_,_,raw_ds,_,_)` >>
  `MEM (pref,k) (abi_entries args raw_ds)` by
    gvs[subst_consts_fn_mods_def, abi_entries_member] >>
  gvs[subst_consts_fn_mods_def] >>
  simp[abi_deployed_signatures_def]
  >- (disj2_tac >>
      qpat_assum `!exports src mut nr rr name args ds ret body pref k. _` drule_all >> simp[]) >>
  disj1_tac >>
  `MEM (name,MAP SND pref) (abi_external_signatures (main_module mods))` suffices_by
    (Cases_on `ALOOKUP mods NONE` >> simp[main_module_def, abi_external_signatures_def])
  >- (qpat_assum `!tops mut nr rr name args ds ret body pref k. MEM _ (FST _) /\ _ ==> _`
        (qspec_then `main_module mods` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  fs[MEM_public_getters] >>
  rename1 `public_getter top = SOME _` >>
  drule publicGetterPropsTheory.public_getter_defaults >> strip_tac >>
  drule publicGetterPropsTheory.public_getter_signature >> strip_tac >>
  gvs[abi_entries_no_defaults, abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `abi_decl_signatures top` >>
  conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]
QED
