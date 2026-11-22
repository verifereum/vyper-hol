(* Tagged getters selected by the linked ABI and compiler classifier. *)
Theory defaultDispatchModsGetter
Ancestors
  compileUnit checkedSelectorTableProps entryDispatchProps e2eModsDefs
  publicGetterProps vyperTypeContractGetter venomFnInstsProofs
  vyperGetter compileVyper vyperABIEntries vyperTypeContract list alist pair
Libs
  BasicProvers

(* Changing the root of a getter changes its expression, not its parameters. *)
Theorem build_getter_args_root_irrelevant[local]:
  !e kt vt n e'.
    FST (build_getter e kt vt n) = FST (build_getter e' kt vt n)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  simp[SimpLHS, Once build_getter_def] >>
  simp[SimpRHS, Once build_getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >> metis_tac[FST]
QED

Theorem tagged_getter_source_tuple[local]:
  !src top mut nr rr name args dflts ret body.
    public_getter_src src top = SOME (mut,nr,rr,name,args,dflts,ret,body) <=>
    rr = F /\ is_public_getter_decl name top /\
    external_getter_tuple src top = SOME (mut,nr,args,dflts,ret,body)
Proof
  rpt gen_tac >> Cases_on `top` >>
  simp[public_getter_src_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  Cases_on `v` >>
  simp[public_getter_src_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  rpt CASE_TAC >> simp[getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem tagged_getter_decl_signature:
  !src top m n r name a ds ret b.
    public_getter_src src top = SOME (m,n,r,name,a,ds,ret,b) ==>
    abi_decl_signatures top = [(name,MAP SND a)]
Proof
  rpt gen_tac >> Cases_on `top` >> simp[public_getter_src_def] >> Cases_on `v` >>
  simp[public_getter_src_def] >> rpt CASE_TAC >> simp[getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
  >- (Cases_on `ret` >> gvs[abi_decl_signatures_def, abi_array_getter_args_def,
                            vyperASTTheory.is_ArrayT_def]) >>
  irule public_getter_signature >>
  simp[public_getter_def, getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[build_getter_args_root_irrelevant, FST]
QED

Theorem tagged_getter_name_key[local]:
  public_getter_src src top = SOME g ==>
  MEM (src,fn_decl_name g) (external_name_keys_toplevel src top)
Proof
  PairCases_on `g` >> simp[tagged_getter_source_tuple, fn_decl_name_def] >>
  Cases_on `top` >> simp[is_public_getter_decl_def] >> Cases_on `v` >>
  simp[is_public_getter_decl_def, external_name_keys_toplevel_def]
QED

Theorem no_explicit_default_in_external_fold[local]:
  FILTER (\f. fn_decl_name f = "__default__")
    (FST (FOLDR classify_function ([],[],NONE,NONE) tops)) = []
Proof
  Induct_on `tops` >> simp[classify_function_external_component] >>
  Cases_on `h` >> simp[] >> Cases_on `f` >> simp[fn_decl_name_def] >>
  IF_CASES_TAC >> simp[fn_decl_name_def]
QED

Theorem exported_default_getter[local]:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops)) /\
  MEM top tops /\ public_getter_src src top = SOME g /\
  fn_decl_name g = "__default__" ==>
  exported_fn src tops "__default__" = [(src,g)]
Proof
  strip_tac >> simp[exported_fn_def] >> pairarg_tac >> gvs[] >>
  drule_then assume_tac tagged_getter_name_key >>
  mp_tac no_explicit_default_in_external_fold >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `FILTER P (FLAT (MAP G tops))` >>
  `MEM g (FILTER P (FLAT (MAP G tops)))` by
    (simp[MEM_FILTER, MEM_FLAT, MEM_MAP, Abbr `P`, Abbr `G`] >>
     qexists_tac `[g]` >> simp[] >> qexists_tac `top` >> simp[]) >>
  Cases_on `FILTER P (FLAT (MAP G tops))` >> gvs[] >>
  rename1 `FILTER P (FLAT (MAP G tops)) = h :: rest` >>
  `MEM h (FILTER P (FLAT (MAP G tops)))` by simp[] >>
  qpat_x_assum `MEM h (FILTER _ _)` mp_tac >>
  simp[MEM_FILTER, MEM_FLAT, MEM_MAP, Abbr `P`, Abbr `G`] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule_then assume_tac tagged_getter_name_key >>
  `t = top` by
    (irule (INST_TYPE [alpha |-> ``:toplevel``, beta |-> ``:num option # string``]
       all_distinct_flat_map_unique) >>
     map_every qexists_tac [`external_name_keys_toplevel src`, `tops`,
                            `(src,"__default__")`] >> simp[] >>
     qpat_x_assum `MEM (src,fn_decl_name _) (external_name_keys_toplevel src t)`
       mp_tac >> simp[]) >>
  gvs[]
QED

Theorem exported_fns_lookup_mem[local]:
  !exps n tops g.
    ALOOKUP exps name = SOME n /\ ALOOKUP mods (SOME n) = SOME tops /\
    MEM (SOME n,g) (exported_fn (SOME n) tops name) ==>
    MEM (SOME n,g) (exported_fns mods exps)
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[exported_fns_def, ALOOKUP_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem selected_default_getter_classified:
  !mods exps am tx tops top mut nr args ret fbody.
    classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
    source_typing_ok_mods mods exps am tx /\
    ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops /\ MEM top tops /\
    is_public_getter_decl "__default__" top /\
    external_getter_tuple (ALOOKUP exps "__default__" ) top = SOME (mut,nr,args,([]:expr
      list),ret,fbody) ==>
    abi_decl_signatures top = [("__default__",MAP SND args)] /\
    MEM (ALOOKUP exps "__default__",subst_consts_fn_mods (consts_env_mods mods)
               (mut,nr,F,"__default__",args,([]:expr list),ret,fbody)) exts
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `src = ALOOKUP exps "__default__"` >>
  qabbrev_tac `g = (mut,nr,F,"__default__",args,([]:expr list),ret,fbody)` >>
  `public_getter_src src top = SOME g` by
    simp[Abbr `g`, tagged_getter_source_tuple] >>
  conj_tac
  >- (qpat_assum `public_getter_src _ _ = _` mp_tac >>
      simp[Abbr `g`] >> metis_tac[tagged_getter_decl_signature]) >>
  qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
  simp[classify_functions_unit_def, Excl "MAP_APPEND"] >>
  pairarg_tac >> gvs[Excl "MAP_APPEND"] >> strip_tac >>
  qpat_x_assum `MAP _ _ = exts` (SUBST1_TAC o SYM) >>
  simp[MEM_MAP, Excl "MAP_APPEND"] >> qexists_tac `(src,g)` >> simp[] >>
  Cases_on `src`
  >- (simp[main_module_def, MEM_MAP] >> disj2_tac >>
      disj2_tac >> simp[MEM_public_getters] >> qexists_tac `top` >>
      gvs[Abbr `g`, tagged_getter_source_tuple, public_getter_source_tuple]) >>
  disj1_tac >> irule exported_fns_lookup_mem >>
  map_every qexists_tac [`"__default__"`, `tops`] >>
  simp[] >> rename1 `ALOOKUP mods (SOME n) = SOME tops` >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (SOME n)) tops))` by
    (fs[source_typing_ok_mods_def] >>
     metis_tac[ALOOKUP_MEM, check_contract_external_names_distinct,
               vyperTypeContractTheory.contract_keys_module_distinct]) >>
  `fn_decl_name g = "__default__"` by simp[Abbr `g`, fn_decl_name_def] >>
  drule_all exported_default_getter >> simp[]
QED
