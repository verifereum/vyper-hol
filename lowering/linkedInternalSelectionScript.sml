(* Recover the qualified source declaration from a packaged internal id. *)
Theory linkedInternalSelection
Ancestors
  linkedFunctionIds linkedNsidProps compileUnit compileVyper constSubstMods
  loweringShapeProps supportedNames alist list pair option

Theorem checked_classified_internal_id_unique:
  ALL_DISTINCT (MAP FST mods) /\
  (!s ts. ALOOKUP mods s = SOME ts ==> supported_declaration_names ts) /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  ALOOKUP mods src = SOME tops /\ vis <> External /\
  MEM (FunctionDecl vis mut nr rr fname args dflts ret stmts) tops /\
  MEM (src',picked) (ints ++ imp_ctors) /\
  build_func_ids_mods 0 mods (nsid_to_string (src',fn_decl_name picked)) =
  build_func_ids_mods 0 mods (nsid_to_string (src,fname)) ==>
  (src',picked) =
  (src,subst_consts_fn_mods (consts_env_mods mods)
    (mut,nr,rr,fname,args,dflts,ret,stmts))
Proof
  `!ts fm nr rr name args defaults ret stmts.
    SND (SND (SND (FOLDR classify_function ([],[],NONE,NONE) ts))) =
      SOME (fm,nr,rr,name,args,defaults,ret,stmts) ==>
    MEM (FunctionDecl Deploy fm nr rr name args defaults ret stmts) ts` by
    (Induct >> simp[] >> rpt gen_tac >>
     qmatch_goalsub_abbrev_tac `classify_function h tail` >>
     PairCases_on `tail` >> Cases_on `h` >>
     simp[classify_function_def] >>
     rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
     Cases_on `vis` >> simp[classify_function_def] >>
     IF_CASES_TAC >> simp[]) >>
  `!ms:(num option # toplevel list) list. !s fm nr rr name args defaults ret stmts.
    MEM (s,fm,nr,rr,name,args,defaults,ret,stmts) (unit_internal_fns ms) ==>
    ?ts. MEM (s,ts) ms /\
      MEM (FunctionDecl Internal fm nr rr name args defaults ret stmts) ts` by
    (Induct >> simp[unit_internal_fns_def] >>
     qx_gen_tac `head` >> PairCases_on `head` >>
     qx_genl_tac [`skey`,`fmut`,`fnr`,`frr`,`fname`,`fargs`,`fdflts`,`fret`,`fstmts`] >>
     simp[unit_internal_fns_def] >>
     Cases_on `FOLDR classify_function ([],[],NONE,NONE) head1` >>
     rename1 `FOLDR _ _ _ = classified` >> PairCases_on `classified` >>
     simp[MEM_MAP] >> rpt strip_tac >> gvs[]
     >- (qexists_tac `head1` >> simp[] >>
         mp_tac (Q.SPECL [`head1`,`fmut`,`fnr`,`frr`,`fname`,`fargs`,
                           `fdflts`,`fret`,`fstmts`] classify_fold_internal) >>
         simp[]) >>
     res_tac >> goal_assum (drule_at Any) >> simp[]) >>
  `!ms:(num option # toplevel list) list. !s fm nr rr name args defaults ret stmts.
    MEM (s,fm,nr,rr,name,args,defaults,ret,stmts) (imported_ctors ms) ==>
    ?ts. MEM (s,ts) ms /\
      MEM (FunctionDecl Deploy fm nr rr name args defaults ret stmts) ts` by
    (Induct >> simp[imported_ctors_def] >>
     qx_gen_tac `head` >> PairCases_on `head` >>
     qx_genl_tac [`skey`,`fmut`,`fnr`,`frr`,`fname`,`fargs`,`fdflts`,`fret`,`fstmts`] >>
     simp[imported_ctors_def] >>
     Cases_on `FOLDR classify_function ([],[],NONE,NONE) head1` >>
     rename1 `FOLDR _ _ _ = classified` >> PairCases_on `classified` >>
     Cases_on `head0` >> Cases_on `classified3` >> simp[] >>
     rpt strip_tac >> gvs[] >>
     res_tac
     >>~- ([`MEM (skey,fmut,fnr,frr,fname,fargs,fdflts,fret,fstmts) (imported_ctors ms)`],
            qexists_tac `ts` >> simp[])
     >> qexists_tac `head1` >> simp[]
     >> qpat_assum `!ts fm nr rr name args defaults ret stmts. SND _ = SOME _ ==> _`
          (qspecl_then [`head1`,`fmut`,`fnr`,`frr`,`fname`,`fargs`,`fdflts`,`fret`,`fstmts`] mp_tac)
     >> simp[]) >>
  `!ms:(num option # toplevel list) list. !s fm nr rr name args defaults ret stmts.
    MEM (s,fm,nr,rr,name,args,defaults,ret,stmts)
      (unit_internal_fns ms ++ imported_ctors ms) ==>
    ?ts vis. MEM (s,ts) ms /\ vis <> External /\
      MEM (FunctionDecl vis fm nr rr name args defaults ret stmts) ts` by
    (rpt gen_tac >> simp[MEM_APPEND] >>
     disch_then DISJ_CASES_TAC
     >- (`?w. MEM (s,w) ms /\
             MEM (FunctionDecl Internal fm nr rr name args defaults ret stmts) w` by
           (first_assum (fn origin => MATCH_MP_TAC (SPEC_ALL origin)) >>
            first_assum ACCEPT_TAC) >>
         qexistsl_tac [`w`,`Internal`] >> simp[])
     >> `?w. MEM (s,w) ms /\
             MEM (FunctionDecl Deploy fm nr rr name args defaults ret stmts) w` by
           (first_assum (fn origin => MATCH_MP_TAC (SPEC_ALL origin)) >>
            first_assum ACCEPT_TAC)
     >> qexistsl_tac [`w`,`Deploy`] >> simp[]) >>
  qabbrev_tac `fn_names = \top.
    case top of FunctionDecl _ _ _ _ name _ _ _ _ => [name] | _ => []` >>
  `!ts. supported_function_names ts = FLAT (MAP fn_names ts)` by
    (Induct >> simp[supported_function_names_def] >> Cases_on `h` >>
     simp[supported_function_names_def, Abbr `fn_names`]) >>
  `!ts name x y.
    ALL_DISTINCT (FLAT (MAP fn_names ts)) /\ MEM x ts /\ MEM y ts /\
    MEM name (fn_names x) /\ MEM name (fn_names y) ==> x = y` by
    (Induct >> simp[ALL_DISTINCT_APPEND] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     Cases_on `x = h` >> Cases_on `y = h` >> fs[] >>
     metis_tac[MEM_FLAT, MEM_MAP]) >>
  `!ts vis1 fm1 nr1 rr1 name args1 ds1 ret1 ss1
       vis2 fm2 nr2 rr2 args2 ds2 ret2 ss2.
    ALL_DISTINCT (supported_function_names ts) /\
    MEM (FunctionDecl vis1 fm1 nr1 rr1 name args1 ds1 ret1 ss1) ts /\
    MEM (FunctionDecl vis2 fm2 nr2 rr2 name args2 ds2 ret2 ss2) ts ==>
    FunctionDecl vis1 fm1 nr1 rr1 name args1 ds1 ret1 ss1 =
      FunctionDecl vis2 fm2 nr2 rr2 name args2 ds2 ret2 ss2` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!ts name x y. ALL_DISTINCT (FLAT (MAP fn_names ts)) /\ _ ==> x = y`
       irule >>
     conj_tac >- (qexists_tac `name` >> simp[Abbr `fn_names`]) >>
     qexists_tac `ts` >>
     qpat_assum `!ts. supported_function_names ts = FLAT (MAP fn_names ts)`
       (qspec_then `ts` (fn th => fs[GSYM th]))) >>
  strip_tac >>
  `?raw. MEM (src',raw) (unit_internal_fns mods ++ imported_ctors mods) /\
      picked = subst_consts_fn_mods (consts_env_mods mods) raw` by
    (qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
     simp[classify_functions_unit_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     `ints ++ imp_ctors =
       MAP (\(s,f). (s,subst_consts_fn_mods (consts_env_mods mods) f))
           (unit_internal_fns mods ++ imported_ctors mods)` by
       simp[MAP_APPEND] >>
     qpat_x_assum `MEM (src',picked) _` mp_tac >>
     qpat_assum `ints ++ imp_ctors = _` (fn membership => PURE_REWRITE_TAC [membership]) >>
     simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
     gvs[] >> metis_tac[]) >>
  PairCases_on `raw` >>
  qpat_assum `!ms:(num option # toplevel list) list. !s fm nr rr name args defaults ret stmts. MEM _ _ ==> _`
    (drule_then strip_assume_tac) >>
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `ALOOKUP mods src' = SOME ts` by
    metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  `fn_decl_name picked = raw3` by simp[subst_consts_fn_mods_def, fn_decl_name_def] >>
  qpat_assum `fn_decl_name picked = raw3` (fn name_eq =>
    qpat_x_assum `build_func_ids_mods 0 mods _ = _`
      (assume_tac o REWRITE_RULE [name_eq])) >>
  `nsid_to_string (src',raw3) = nsid_to_string (src,fname)` by
    (mp_tac (Q.SPECL [`mods`,`0`,`src'`,`ts`,`vis'`,`raw0`,`raw1`,`raw2`,
        `raw3`,`raw4`,`raw5`,`raw6`,`raw7`,
        `src`,`tops`,`vis`,`mut`,`nr`,`rr`,`fname`,`args`,`dflts`,`ret`,`stmts`]
        build_func_ids_mods_11) >> simp[]) >>
  `!ts vis mut nr rr name args dflts ret stmts.
       supported_declaration_names ts /\
       MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) ts ==>
       ~MEM #"." name` by
    (map_every qx_gen_tac [`module_tops`,`visibility`,`mutability`,
       `nonreentrant`,`raw_return`,`name`,`params`,`defs`,`result`,`body_stmt_list`] >>
     rewrite_tac[supported_declaration_names_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `EVERY (\tl. ~MEM #"." _) module_tops`
       (mp_tac o Q.SPEC
          `FunctionDecl visibility mutability nonreentrant raw_return name params defs result body_stmt_list`
        o REWRITE_RULE [EVERY_MEM]) >>
     asm_simp_tac (srw_ss()) []) >>
  `supported_declaration_names ts` by
    (qpat_assum `!s ts. ALOOKUP mods s = SOME ts ==> _`
       (qspec_then `src'` (qspec_then `ts` mp_tac)) >> simp[]) >>
  `supported_declaration_names tops` by
    (qpat_assum `!s ts. ALOOKUP mods s = SOME ts ==> _`
       (qspec_then `src` (qspec_then `tops` mp_tac)) >> simp[]) >>
  `~MEM #"." raw3` by
    (qpat_assum `!ts vis mut nr rr name args dflts ret stmts. _ ==> ~MEM #"." name`
       (qspecl_then [`ts`,`vis'`,`raw0`,`raw1`,`raw2`,`raw3`,
                    `raw4`,`raw5`,`raw6`,`raw7`] mp_tac) >> simp[]) >>
  `~MEM #"." fname` by
    (qpat_assum `!ts vis mut nr rr name args dflts ret stmts. _ ==> ~MEM #"." name`
       (qspecl_then [`tops`,`vis`,`mut`,`nr`,`rr`,`fname`,
                    `args`,`dflts`,`ret`,`stmts`] mp_tac) >> simp[]) >>
  `(src',raw3) = (src,fname)` by
    (irule nsid_to_string_dot_free_injective >> simp[]) >>
  gvs[] >>
  `ALL_DISTINCT (FLAT (MAP fn_names tops))` by
    (qpat_assum `!ts. supported_function_names ts = _`
       (fn names_eq => PURE_REWRITE_TAC [GSYM (Q.SPEC `tops` names_eq)]) >>
     fs[supported_declaration_names_def]) >>
  qpat_assum `!ts vis1 fm1 nr1 rr1 name args1 ds1 ret1 ss1
            vis2 fm2 nr2 rr2 args2 ds2 ret2 ss2. _`
    (qspec_then `tops` mp_tac) >>
  disch_then (qspecl_then [`vis'`,`raw0`,`raw1`,`raw2`,`fname`,`raw4`,
    `raw5`,`raw6`,`raw7`,`vis`,`mut`,`nr`,`rr`,`args`,`dflts`,`ret`,`stmts`] mp_tac) >>
  simp[] >> strip_tac >> simp[]
QED
