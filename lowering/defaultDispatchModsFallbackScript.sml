(* The installed fallback is the explicit default declaration in the module
   selected by the source export lookup. *)
Theory defaultDispatchModsFallback
Ancestors
  alist compileUnit compileVyper constSubstMods e2eModsDefs list
  defaultDispatchModsNames entryDispatchProps loweringShapeProps supportedNames venomFnInstsProofs
  vyperCalldata vyperInterpreter vyperTypeContract vyperTypeContractGetter

Theorem fallback_fold_slot[local]:
  !tops.
    (FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) = NONE ==>
       ~(list$EXISTS is_default_decl tops)) /\
    (!m nr rr nm aa ds r b.
       FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) =
          SOME (m,nr,rr,nm,aa,ds,r,b) ==> nm = "__default__")
Proof
  Induct >- simp[] >> gen_tac >>
  qabbrev_tac `fold = FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `fold` >> gvs[GSYM markerTheory.Abbrev_def] >>
  Cases_on `h` >>
  TRY (rename1 `FunctionDecl vis` >> Cases_on `vis`) >>
  pure_rewrite_tac[classify_function_def, is_default_decl_def,
    pairTheory.FST, pairTheory.SND, vyperASTTheory.function_visibility_case_def] >>
  TRY (rename1 `if nm = "__default__" then _ else _` >>
       Cases_on `nm = "__default__"` >> asm_rewrite_tac[]) >>
  simp_tac std_ss [] >> metis_tac[]
QED

Theorem exported_fallback_slot:
  !exps src f.
    exported_fallback mods exps = SOME (src,f) ==>
    ?n tops. src = SOME n /\ MEM ("__default__",n) exps /\
      ALOOKUP mods src = SOME tops /\
      FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) = SOME f
Proof
  Induct >- simp[exported_fallback_def] >>
  gen_tac >> PairCases_on `h` >> rename1 `(name,n)::exps` >>
  Cases_on `name = "__default__"` >> gvs[exported_fallback_def]
  >- (Cases_on `ALOOKUP mods (SOME n)` >> gvs[]
      >- metis_tac[] >>
      rename1 `ALOOKUP mods (SOME n) = SOME tops` >>
      qabbrev_tac `fold = FOLDR classify_function ([],[],NONE,NONE) tops` >>
      PairCases_on `fold` >> Cases_on `fold2` >>
      gvs[GSYM markerTheory.Abbrev_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem chosen_fallback_slot[local]:
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  (MEM "__default__" (MAP FST exps) ==>
     ~MEM (NONE,"__default__")
       (FLAT (MAP (external_name_keys_toplevel NONE) (main_module mods)))) /\
  ALL_DISTINCT (MAP FST exps) /\
  ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops /\
  (list$EXISTS is_default_decl (main_module mods) \/ IS_SOME (exported_fallback mods exps)) ==>
  ?m nr rr args ds ret body.
    MEM (FunctionDecl External m nr rr "__default__" args ds ret body) tops /\
    fb = SOME (ALOOKUP exps "__default__", subst_consts_fn_mods (consts_env_mods mods)
                  (m,nr,rr,"__default__",args,ds,ret,body))
Proof
  simp[classify_functions_unit_def] >> rpt (pairarg_tac >> gvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `FOLDR classify_function _ (main_module mods) = (_,_,mainfb,_)` >>
  Cases_on `mainfb` >> simp[]
  >- (`~list$EXISTS is_default_decl (main_module mods)` by
        (qspec_then `main_module mods` mp_tac fallback_fold_slot >> simp[]) >>
      `?src f. exported_fallback mods exps = SOME (src,f)` by
        (Cases_on `exported_fallback mods exps` >> gvs[] >> PairCases_on `x` >>
         metis_tac[]) >>
      drule exported_fallback_slot >> strip_tac >>
      `ALOOKUP exps "__default__" = SOME n` by
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
      gvs[] >> PairCases_on `f` >>
      drule classify_fold_fallback_mem >> strip_tac >>
      qspec_then `tops` mp_tac fallback_fold_slot >> simp[] >> metis_tac[]) >>
  rename1 `FOLDR classify_function _ (main_module mods) = (_,_,SOME raw,_)` >>
  `FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) (main_module mods)))) = SOME raw` by simp[] >>
  PairCases_on `raw` >>
  drule classify_fold_fallback_mem >> strip_tac >>
  `raw3 = "__default__"` by
    (qspec_then `main_module mods` mp_tac fallback_fold_slot >> simp[]) >> gvs[] >>
  `MEM (NONE,"__default__")
    (FLAT (MAP (external_name_keys_toplevel NONE) (main_module mods)))` by
    (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> goal_assum (drule_at Any) >>
     simp[external_name_keys_toplevel_def]) >>
  `ALOOKUP exps "__default__" = NONE` by metis_tac[ALOOKUP_NONE] >>
  gvs[main_module_def] >> metis_tac[]
QED

Theorem fallback_decl_agrees[local]:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops)) /\
  MEM (FunctionDecl External m nr rr "__default__" aa ds r b) tops /\
  vyperInterpreter$lookup_function src "__default__" External tops =
    SOME (mut,guarded,args,[],ret,fbody) ==>
  (m,nr,rr,"__default__",aa,ds,r,b) =
    (mut,guarded,lookup_raw_return_or_F src "__default__" External tops,
      "__default__",args,([]:expr list),ret,fbody)
Proof
  strip_tac >> drule lookup_function_external_raw_cases >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (`FunctionDecl External m nr rr "__default__" aa ds r b =
         FunctionDecl External mut guarded rr' "__default__" args [] ret fbody` by
        (drule all_distinct_flat_map_unique >>
         disch_then irule >> simp[external_name_keys_toplevel_def]) >>
      gvs[lookup_raw_return_or_F_def]) >>
  `MEM (src,"__default__") (external_name_keys_toplevel src decl)` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def] >>
     Cases_on `v` >> gvs[is_public_getter_decl_def, external_name_keys_toplevel_def]) >>
  `decl = FunctionDecl External m nr rr "__default__" aa ds r b` by
    (drule all_distinct_flat_map_unique >>
     disch_then irule >> simp[external_name_keys_toplevel_def]) >>
  gvs[is_public_getter_decl_def]
QED

Theorem default_miss_classified:
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  source_typing_ok_mods mods exps am tx /\
  (MEM "__default__" (MAP FST exps) ==>
     ~MEM (NONE,"__default__")
       (FLAT (MAP (external_name_keys_toplevel NONE) (main_module mods)))) /\
  ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops /\
  vyperInterpreter$lookup_function (ALOOKUP exps "__default__") "__default__" External tops =
    SOME (mut,guarded,args,[],ret,fbody) /\
  (list$EXISTS is_default_decl (main_module mods) \/ IS_SOME (exported_fallback mods exps)) ==>
  args = [] /\
  fb = SOME (ALOOKUP exps "__default__" , (mut,guarded,lookup_raw_return_or_F (ALOOKUP exps
    "__default__" ) "__default__" External tops,
     "__default__",args,([]:expr list),ret,
     subst_consts_stmts_mods (consts_env_mods mods) fbody))
Proof
  mp_tac chosen_fallback_slot >>
  simp[] >> disch_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all source_typing_ok_mods_external_names_distinct >> strip_tac >>
  qpat_x_assum `source_typing_ok_mods _ _ _ _` mp_tac >>
  simp[source_typing_ok_mods_def] >> strip_tac >>
  drule_then strip_assume_tac exports_ok_names >>
  first_x_assum drule_all >> strip_tac >>
  `MEM (ALOOKUP exps "__default__",tops) mods` by metis_tac[ALOOKUP_MEM] >>
  drule_all fallback_decl_agrees >> strip_tac >>
  gvs[subst_consts_fn_mods_def, subst_consts_expr_mods_def] >>
  drule_all check_contract_function_header >>
  metis_tac[supported_fallback_no_arguments]
QED
