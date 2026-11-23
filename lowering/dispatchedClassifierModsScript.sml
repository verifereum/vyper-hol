Theory dispatchedClassifierMods
Ancestors
  compileUnit compileVyper defaultDispatchModsGetter defaultDispatchModsNames entryDispatchProps loweringShapeProps e2eModsDefs
  vyperTypeContract vyperGetter vyperAST venomFnInstsProofs constSubstMods
  alist list pair
Libs
  BasicProvers

val _ = Parse.hide "body";

Theorem getter_tag_none[local]:
  public_getter_src NONE top = public_getter top
Proof
  Cases_on `top` >> simp[public_getter_src_def, public_getter_def] >>
  Cases_on `v` >> simp[public_getter_src_def, public_getter_def]
QED

Theorem tagged_getter_list_mem[local]:
  MEM g (FLAT (MAP (\t. case public_getter_src src t of
                            NONE => [] | SOME f => [f]) tops)) <=>
  ?t. MEM t tops /\ public_getter_src src t = SOME g
Proof
  `!t. MEM g (case public_getter_src src t of NONE => [] | SOME f => [f]) <=>
       public_getter_src src t = SOME g` by
    (gen_tac >> Cases_on `public_getter_src src t` >> simp[EQ_SYM_EQ]) >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, CONJ_COMM]
QED

(* Checked keys force the first matching exported candidate to be the
   selected declaration, regardless of the order of the module's tops. *)
Theorem exported_fn_selected[local]:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops)) /\
  MEM top tops /\
  ((name <> "__default__" /\ top = FunctionDecl External m n r name a d t b) \/
   public_getter_src src top = SOME (m,n,r,name,a,d,t,b)) ==>
  MEM (src,(m,n,r,name,a,d,t,b)) (exported_fn src tops name)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM (src,name) (external_name_keys_toplevel src top)` by
    (qpat_x_assum `(name <> _ /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
     >- gvs[external_name_keys_toplevel_def] >>
     drule tagged_getter_name_key >> simp[fn_decl_name_def]) >>
  `!u. MEM u tops /\ MEM (src,name) (external_name_keys_toplevel src u) ==> u = top` by
    metis_tac[all_distinct_flat_map_unique] >>
  simp[exported_fn_def] >> pairarg_tac >>
  rename1 `FOLDR classify_function ([],[],NONE,NONE) tops = (es,is,fb,ct)` >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `FILTER p es` >>
  Cases_on `FILTER p es` >> simp[]
  >- (
    `public_getter_src src top = SOME (m,n,r,name,a,d,t,b)` by
      (gvs[] >>
       `MEM (m,n,r,name,a,d,t,b) (FILTER p es)` suffices_by simp[] >>
       simp[MEM_FILTER, Abbr `p`, fn_decl_name_def] >>
       qspec_then `tops` mp_tac classify_fold_external_member >> simp[]) >>
    qmatch_goalsub_abbrev_tac `FILTER p gs` >>
    `MEM (m,n,r,name,a,d,t,b) (FILTER p gs)` by
      (simp[MEM_FILTER, Abbr `p`, fn_decl_name_def, Abbr `gs`, tagged_getter_list_mem] >>
       metis_tac[]) >>
    Cases_on `FILTER p gs` >> gvs[] >>
    rename1 `FILTER p gs = g :: rest` >>
    `MEM g (FILTER p gs)` by simp[] >>
    PairCases_on `g` >>
    gvs[MEM_FILTER, Abbr `p`, fn_decl_name_def, Abbr `gs`,
        tagged_getter_list_mem, public_getter_src_def] >>
    rename1 `public_getter_src src u = SOME (g0,g1,g2,_,g4,g5,g6,g7)` >>
    qpat_assum `public_getter_src _ u = _`
      (assume_tac o SIMP_RULE std_ss [fn_decl_name_def] o MATCH_MP tagged_getter_name_key) >>
    `u = top` by (first_x_assum irule >> simp[]) >> gvs[]) >>
  rename1 `FILTER p es = g :: rest` >>
  `MEM g (FILTER p es)` by simp[] >> PairCases_on `g` >>
  fs[MEM_FILTER, Abbr `p`, fn_decl_name_def] >>
  `MEM (FunctionDecl External g0 g1 g2 g3 g4 g5 g6 g7) tops` by
    (qspec_then `tops` mp_tac classify_fold_external_source >> simp[]) >>
  `FunctionDecl External g0 g1 g2 g3 g4 g5 g6 g7 = top` by
    (first_x_assum irule >> simp[external_name_keys_toplevel_def]) >>
  gvs[public_getter_src_def]
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

Theorem selected_external_member_with_defaults_mods:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
  ((name <> "__default__" /\
    top = FunctionDecl External mut nr rr name args dflts ret body) \/
   public_getter_src (ALOOKUP exps name) top =
     SOME (mut,nr,rr,name,args,dflts,ret,body)) /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) ==>
  MEM (ALOOKUP exps name,subst_consts_fn_mods (consts_env_mods mods)
         (mut,nr,rr,name,args,dflts,ret,body)) exts
Proof
  strip_tac >>
  qabbrev_tac `src = ALOOKUP exps name` >>
  qabbrev_tac `g = (mut,nr,rr,name,args,dflts,ret,body)` >>
  `MEM (src,g) (exported_fns mods exps ++ MAP (\f. (NONE,f))
      (FST (FOLDR classify_function ([],[],NONE,NONE) (main_module mods)) ++
       public_getters (main_module mods)))` by (
    Cases_on `src`
    >- (simp[main_module_def, MEM_MAP, Abbr `g`] >>
        gvs[] >> metis_tac[classify_fold_external_member, MEM_public_getters, getter_tag_none]) >>
    simp[MEM_APPEND, MEM_MAP] >>
    irule exported_fns_lookup_mem >>
    qexistsl_tac [`name`,`tops`] >>
    fs[markerTheory.Abbrev_def, Abbr `g`] >>
    irule exported_fn_selected >>
    metis_tac[source_typing_ok_mods_external_names_distinct]) >>
  qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
  simp[classify_functions_unit_def, Excl "MAP_APPEND"] >>
  pairarg_tac >> simp[Excl "MAP_APPEND"] >> strip_tac >>
  qpat_x_assum `MAP _ _ = exts` (SUBST1_TAC o SYM) >>
  simp[MEM_MAP, Excl "MAP_APPEND", Excl "MEM_APPEND"] >>
  qexists_tac `(src,g)` >> fs[MEM_APPEND, MEM_MAP, Abbr `g`]
QED

Theorem selected_external_member_mods:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
  ((name <> "__default__" /\
    top = FunctionDecl External mut nr rr name args [] ret b) \/
   public_getter_src (ALOOKUP exps name) top = SOME (mut,nr,rr,name,args,([]:expr list),ret,b)) /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) ==>
  MEM (ALOOKUP exps name,subst_consts_fn_mods (consts_env_mods mods)
         (mut,nr,rr,name,args,([]:expr list),ret,b)) exts
Proof
  MATCH_ACCEPT_TAC selected_external_member_with_defaults_mods
QED
