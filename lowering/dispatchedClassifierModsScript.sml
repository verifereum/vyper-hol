Theory dispatchedClassifierMods
Ancestors
  compileUnit compileVyper entryDispatchProps loweringShapeProps e2eModsDefs
  vyperTypeContract vyperGetter vyperAST venomFnInstsProofs constSubstMods
  alist list pair
Libs
  BasicProvers

Theorem getter_tag_none[local]:
  public_getter_src NONE top = public_getter top
Proof
  Cases_on `top` >> simp[public_getter_src_def, public_getter_def] >>
  Cases_on `v` >> simp[public_getter_src_def, public_getter_def]
QED

Theorem getter_has_external_key[local]:
  public_getter_src src top = SOME (m,n,r,name,a,d,t,b) ==>
  external_name_keys_toplevel src top = [(src,name)]
Proof
  Cases_on `top` >> simp[public_getter_src_def] >> Cases_on `v` >>
  simp[public_getter_src_def, external_name_keys_toplevel_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[])
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
  disch_then (CONJUNCTS_THEN assume_tac) >>
  `MEM (src,name) (external_name_keys_toplevel src top)` by
    (gvs[] >> metis_tac[getter_has_external_key, external_name_keys_toplevel_def, MEM]) >>
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
      (assume_tac o MATCH_MP getter_has_external_key) >>
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

Theorem selected_external_member_mods:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\ MEM top tops /\
  ((name <> "__default__" /\ ?rr. top = FunctionDecl External mut nr rr name args [] ret b) \/
   public_getter_src (ALOOKUP exps name) top = SOME (mut,nr,F,name,args,([]:expr list),ret,b)) /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) ==>
  ?rr b'. MEM (ALOOKUP exps name,(mut,nr,rr,name,args,([]:expr list),ret,b')) exts
Proof
  simp[] >> strip_tac >>
  qabbrev_tac `src = ALOOKUP exps name` >>
  `?r. (name <> "__default__" /\ top = FunctionDecl External mut nr r name args [] ret b) \/
       public_getter_src src top = SOME (mut,nr,r,name,args,([]:expr list),ret,b)` by metis_tac[] >>
  qabbrev_tac `g = (mut,nr,r,name,args,([]:expr list),ret,b)` >>
  `MEM (src,g) (exported_fns mods exps ++ MAP (\f. (NONE,f))
      (FST (FOLDR classify_function ([],[],NONE,NONE) (main_module mods)) ++
       public_getters (main_module mods)))` by (
    Cases_on `src`
    >- (simp[main_module_def, MEM_MAP, Abbr `g`] >>
        gvs[] >> metis_tac[classify_fold_external_member, MEM_public_getters, getter_tag_none]) >>
    simp[MEM_APPEND, MEM_MAP] >>
    rename1 `ALOOKUP mods (SOME s) = SOME tops` >>
    `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (SOME s)) tops))` by
      (fs[source_typing_ok_mods_def] >>
       metis_tac[ALOOKUP_MEM, check_contract_external_names_distinct, contract_keys_module_distinct]) >>
    `MEM (SOME s,g) (exported_fn (SOME s) tops name)` by
      (simp[Abbr `g`] >> irule exported_fn_selected >> metis_tac[]) >>
    `MEM (name,s) exps` by metis_tac[ALOOKUP_MEM, Abbr `src`] >>
    `!es. MEM (name,s) es ==> MEM (SOME s,g) (exported_fns mods es)` by
      (Induct >> simp[] >> Cases_on `h` >>
       simp[exported_fns_def] >> strip_tac >> gvs[]) >>
    simp[]) >>
  qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
  simp[classify_functions_unit_def, Excl "MAP_APPEND"] >>
  pairarg_tac >> simp[Excl "MAP_APPEND"] >> strip_tac >>
  qpat_x_assum `MAP _ _ = exts` (SUBST1_TAC o SYM) >>
  qexistsl_tac [`r`, `subst_consts_stmts_mods (consts_env_mods mods) b`] >>
  simp[MEM_MAP, Excl "MAP_APPEND", Excl "MEM_APPEND"] >>
  qexists_tac `(src,g)` >> simp[Excl "MEM_APPEND"] >>
  simp[Abbr `g`, subst_consts_fn_mods_def, subst_consts_expr_mods_def] >>
  qpat_x_assum `MEM (src,_) (_ ++ _)` mp_tac >> simp[MEM_MAP]
QED
