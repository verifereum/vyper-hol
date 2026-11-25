Theory linkedEntryBodyTables
Ancestors
  bodyInvCodeProps bodyInvSplit bodyCallSupport linkedNsidProps
  linkedStorageMetadataProps entryDecodePlanProps vyperTypeContractStaticMaps
  vyperTypeContract compileVyper
  vyperTypeInvariants vyperInterpreter vyperState compileUnit
  supportedNames compileEnv loweringShapeProps[qualified] alist list finite_map pair

val _ = Parse.hide "body";
val _ = Parse.hide "member";

Theorem linked_entry_declared_return_type:
  contract_inv mods exps ctx ce cx /\
  ALOOKUP mods src = SOME tops /\ vis <> External /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops ==>
  ce.ce_func_return_type (nsid_to_string (src,name)) = ret
Proof
  strip_tac >>
  `ce.ce_func_return_type = build_func_return_type_mods mods` by
    fs[contract_inv_def] >>
  qpat_assum `contract_inv mods exps ctx ce cx`
    (strip_assume_tac o REWRITE_RULE [contract_inv_def]) >>
  `!s ts. ALOOKUP mods s = SOME ts ==> supported_module_headers ts` by
    (rpt strip_tac >>
     qpat_assum `!s ts. ALOOKUP mods s = SOME ts ==> supported_module_headers ts /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  qabbrev_tac `dot_free_functions = \ts. !v m a b n params defaults r ss.
    MEM (FunctionDecl v m a b n params defaults r ss) ts ==> ~MEM #"." n` >>
  `!s ts. MEM (s,ts) mods ==>
      ALL_DISTINCT (supported_function_names ts) /\ dot_free_functions ts` by
    (rpt strip_tac >>
     `ALOOKUP mods s = SOME ts` by
       (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
     `supported_module_headers ts` by
       (first_assum (drule_then ACCEPT_TAC)) >>
     pop_assum (mp_tac o REWRITE_RULE [supported_module_headers_def,
       supported_declaration_names_def]) >>
     simp[Abbr `dot_free_functions`, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `dot_free_functions tops` by
    (first_assum (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `~MEM #"." name` by
    (pop_assum mp_tac >> simp[Abbr `dot_free_functions`] >>
     disch_then (qspecl_then
       [`vis`,`mut`,`nr`,`rr`,`name`,`args`,`dflts`,`ret`,`body`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `!ts rest. ALL_DISTINCT (supported_function_names ts) /\
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) ts ==>
      build_func_return_type_src src ts rest (nsid_to_string (src,name)) = ret` by
    (Induct >> simp[] >> gen_tac >> Cases_on `h` >>
     simp[build_func_return_type_src_def, supported_function_names_def] >>
     rpt strip_tac >> gvs[] >>
     `MEM name (supported_function_names ts)` by
       (simp[loweringShapePropsTheory.MEM_supported_function_names] >> metis_tac[]) >>
     `name <> s` by (strip_tac >> gvs[]) >>
     Cases_on `f = External` >> Cases_on `src` >>
     fs[nsid_to_string_def]) >>
  `!ts other rest. other <> src /\ dot_free_functions ts ==>
     build_func_return_type_src other ts rest (nsid_to_string (src,name)) =
       rest (nsid_to_string (src,name))` by
    (Induct >- simp[build_func_return_type_src_def] >>
     gen_tac >> rpt gen_tac >> strip_tac >>
     `dot_free_functions ts` by
       (qpat_assum `Abbrev (dot_free_functions = _)` (fn abbrev =>
          let val def = REWRITE_RULE [markerTheory.Abbrev_def] abbrev
          in
            qpat_assum `dot_free_functions (_ :: ts)`
              (mp_tac o REWRITE_RULE [MEM] o BETA_RULE o PURE_REWRITE_RULE [def]) >>
            PURE_REWRITE_TAC [def] >> BETA_TAC
          end) >>
        disch_then (fn dot_free =>
          rpt gen_tac >> strip_tac >>
          MATCH_MP_TAC (SPEC_ALL dot_free) >> simp[])) >>
     `build_func_return_type_src other ts rest (nsid_to_string (src,name)) =
        rest (nsid_to_string (src,name))` by
       (qpat_assum `!s f. _ ==> build_func_return_type_src s ts f _ = f _`
          (MATCH_MP_TAC o SPEC_ALL) >> conj_tac >> first_assum ACCEPT_TAC) >>
     Cases_on `h` >> simp[build_func_return_type_src_def] >>
     `~MEM #"." s` by
       (qpat_assum `Abbrev (dot_free_functions = _)` (fn abbrev =>
          qpat_assum `dot_free_functions (FunctionDecl _ _ _ _ _ _ _ _ _ :: ts)`
            (qspecl_then [`f`,`f0`,`b`,`b0`,`s`,`l`,`l0`,`t`,`l1`] mp_tac o
             BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>
        simp[NoAsms]) >>
     `nsid_to_string (src,name) <> nsid_to_string (other,s)` by
       (strip_tac >>
        `(src,name) = (other,s)` by
          (irule nsid_to_string_dot_free_injective >> simp[]) >>
        fs[]) >>
     Cases_on `f = External` >> simp[]) >>
  `EVERY (\(_,ts). ALL_DISTINCT (supported_function_names ts) /\
      dot_free_functions ts) mods` by
    (simp[NoAsms, EVERY_MEM, FORALL_PROD] >>
     qpat_assum `!s ts. MEM (s,ts) mods ==> _` ACCEPT_TAC) >>
  `!ms. EVERY (\(_,ts). ALL_DISTINCT (supported_function_names ts) /\
      dot_free_functions ts) ms /\ ALOOKUP ms src = SOME tops ==>
      build_func_return_type_mods ms (nsid_to_string (src,name)) = ret` by
    (Induct >- simp[] >>
     gen_tac >> PairCases_on `h` >>
     simp[NoAsms, ALOOKUP_def, build_func_return_type_mods_def] >>
     Cases_on `h0 = src` >> simp[] >> rpt strip_tac >> gvs[]) >>
  qpat_assum `ce.ce_func_return_type = _` SUBST1_TAC >>
  qpat_assum `!ms. _ ==> build_func_return_type_mods ms _ = ret`
    (MATCH_MP_TAC o SPEC_ALL) >> simp[]
QED

Theorem linked_entry_flag_member_id:
  contract_inv mods exps ctx ce cx /\
  contract_namespaces_ok dep mods /\
  get_module_code cx src = SOME tops /\ lookup_flag name tops = SOME members /\
  INDEX_OF member members = SOME index ==>
  ce.ce_flag_member_id (nsid_to_string (src,name)) member = index
Proof
  strip_tac >>
  `ALOOKUP mods src = SOME tops` by
    (qpat_assum `contract_inv mods exps ctx ce cx`
       (qspec_then `src` (SUBST1_TAC o SYM) o MATCH_MP contract_inv_module_codes) >>
     first_assum ACCEPT_TAC) >>
  `contract_namespaces_ok F mods` by
    (Cases_on `dep` >> fs[contract_namespaces_ok_deploy_implies_runtime]) >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  `ce.ce_flag_member_id = FST (build_flag_info_mods mods (K (K 0)) (K 0))` by
    fs[contract_inv_def, cenv_module_pins_mods_def] >>
  `MEM (src,tops) mods` by (drule_then ACCEPT_TAC ALOOKUP_MEM) >>
  `!ts. lookup_flag name ts = SOME members ==> MEM (FlagDecl name members) ts` by
    (Induct >- rw[lookup_flag_def] >> gen_tac >> Cases_on `h` >>
     rw[lookup_flag_def] >> gvs[AllCaseEqs()]) >>
  `MEM (FlagDecl name members) tops` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `!s ts n ms. MEM (s,ts) mods /\ MEM (FlagDecl n ms) ts ==> ~MEM #"." n` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `contract_namespaces_ok F mods`
       (strip_assume_tac o REWRITE_RULE [contract_namespaces_ok_def]) >>
     qpat_x_assum `EVERY (\(s,ts). EVERY _ ts) mods` mp_tac >>
     simp[Once EVERY_MEM] >>
     disch_then (qspec_then `(s,ts)` mp_tac) >> simp[] >>
     simp[Once EVERY_MEM] >>
     disch_then (qspec_then `FlagDecl n ms` mp_tac) >> simp[]) >>
  qabbrev_tac `key = nsid_to_string (src,name)` >>
  `!s ts n ms. MEM (s,ts) mods /\ MEM (FlagDecl n ms) ts /\
       nsid_to_string (s,n) = key ==> ms = members` by
    (rpt gen_tac >> strip_tac >>
     `(s,n) = (src,name)` by
       (irule nsid_to_string_dot_free_injective >>
        simp[GSYM markerTheory.Abbrev_def] >> metis_tac[]) >>
     `ALOOKUP mods s = SOME ts` by (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
     gvs[] >>
     rename1 `ALOOKUP mods selected_src = SOME tops` >>
     `ALL_DISTINCT (FLAT (MAP (flag_member_keys_toplevel selected_src) tops))` by
       (drule_all contract_namespaces_ok_module_flag_member_keys >> simp[]) >>
     `lookup_flag n tops = SOME ms` by
       (irule lookup_flag_MEM_FlagDecl >> conj_tac
        >- (qexists_tac `selected_src` >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     fs[]) >>
  `build_flag_member_id_one members 0 member = index` by
    (qspecl_then [`[FlagDecl name members]`,`K (K 0)`,`K 0`,`name`,
      `members`,`member`,`index`] mp_tac build_flag_info_member_id >>
     simp[build_flag_info_def, lookup_flag_def, type_def_keys_toplevel_def]) >>
  `!ts s ids counts.
     (!n ms. MEM (FlagDecl n ms) ts /\ nsid_to_string (s,n) = key ==> ms = members) ==>
     FST (build_flag_info_src s ts ids counts) key member =
       if (?n ms. MEM (FlagDecl n ms) ts /\ nsid_to_string (s,n) = key)
       then index else ids key member` by
    (Induct >- simp[build_flag_info_src_def] >>
     gen_tac >> Cases_on `h` >> simp[build_flag_info_src_def] >>
     rpt gen_tac >> strip_tac
     >~ [`FST (build_flag_info_src s'' ts
                (\f. if f = nsid_to_string (s'',s)
                  then build_flag_member_id_one l 0 else ids f) _) key member = _`]
     >- (pop_assum (fn all_members => pop_assum (fn ih =>
           qmatch_goalsub_abbrev_tac `build_flag_info_src s'' ts next_ids next_counts` >>
           mp_tac (Q.SPECL [`s''`,`next_ids`,`next_counts`] ih) >>
           impl_tac >- (rpt strip_tac >> MATCH_MP_TAC (SPEC_ALL all_members) >>
             simp[]) >>
           disch_then SUBST1_TAC >>
           simp[Abbr `next_ids`, LEFT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS] >>
           Cases_on `nsid_to_string (s'',s) = key` >> simp[] >>
           assume_tac all_members >> metis_tac[]))) >>
     pop_assum (fn tail_members => pop_assum (fn ih =>
       ACCEPT_TAC (MATCH_MP (Q.SPECL [`s''`,`ids`,`counts`] ih) tail_members)))) >>
  `!ms ids counts.
     (!s ts n xs. MEM (s,ts) ms /\ MEM (FlagDecl n xs) ts /\
        nsid_to_string (s,n) = key ==> xs = members) ==>
     FST (build_flag_info_mods ms ids counts) key member =
       if (?s ts n xs. MEM (s,ts) ms /\ MEM (FlagDecl n xs) ts /\
                        nsid_to_string (s,n) = key)
       then index else ids key member` by
    (Induct >> simp[build_flag_info_mods_def] >>
     gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
     qabbrev_tac `info = build_flag_info_src h0 h1 ids counts` >>
     PairCases_on `info` >>
     `FST (build_flag_info_src h0 h1 ids counts) key member =
       if (?n xs. MEM (FlagDecl n xs) h1 /\ nsid_to_string (h0,n) = key)
       then index else ids key member` by
       (first_assum irule >> metis_tac[MEM]) >>
     simp[build_flag_info_mods_def, GSYM markerTheory.Abbrev_def] >>
     qpat_assum `!ids counts. _` (qspecl_then [`info0`,`info1`] mp_tac) >>
     impl_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[MEM]) >>
     disch_then SUBST1_TAC >>
     `info0 key member = if (?n xs. MEM (FlagDecl n xs) h1 /\
       nsid_to_string (h0,n) = key) then index else ids key member` by
       (qpat_assum `Abbrev ((info0,info1) = _)`
          (SUBST1_TAC o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `FST` o
           PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
        first_assum ACCEPT_TAC) >>
     simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS] >>
     Cases_on `?n xs. MEM (FlagDecl n xs) h1 /\ nsid_to_string (h0,n) = key` >>
     simp[]) >>
  qpat_assum `!ms ids counts. _`
    (qspecl_then [`mods`,`K (K 0)`,`K 0`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (mp_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[GSYM markerTheory.Abbrev_def] >>
  metis_tac[]
QED

Theorem linked_entry_hashmap_info:
  contract_inv mods exps ctx ce cx /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name name tops = SOME (HashMapVarDecl tr kt vt,id) ==>
  ce.ce_hashmap_info (src,name) = SOME (tr,kt,vt)
Proof
  strip_tac >>
  `ALOOKUP mods src = SOME tops` by
    (qpat_assum `contract_inv mods exps ctx ce cx`
       (qspec_then `src` (SUBST1_TAC o SYM) o MATCH_MP contract_inv_module_codes) >>
     first_assum ACCEPT_TAC) >>
  `ce.ce_hashmap_info = build_hashmap_info_mods mods` by
    fs[contract_inv_def] >>
  asm_rewrite_tac[] >>
  `!ts other rest. other <> src ==>
      build_hashmap_info_src other ts rest (src,name) = rest (src,name)` by
    (Induct >> simp[build_hashmap_info_src_def] >>
     Cases >> simp[build_hashmap_info_src_def]) >>
  `!ts rest.
      find_var_decl_by_name name ts = SOME (HashMapVarDecl tr kt vt,id) ==>
      build_hashmap_info_src src ts rest (src,name) = SOME (tr,kt,vt)` by
    (Induct >> simp[find_var_decl_by_name_def, build_hashmap_info_src_def] >>
     Cases >> simp[find_var_decl_by_name_def, build_hashmap_info_src_def] >>
     rpt gen_tac >> IF_CASES_TAC >> simp[]) >>
  `!ms. ALOOKUP ms src = SOME tops ==>
      build_hashmap_info_mods ms (src,name) = SOME (tr,kt,vt)` by
    (Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
     rw[ALOOKUP_def, build_hashmap_info_mods_def]) >>
  first_assum drule >> simp[]
QED
