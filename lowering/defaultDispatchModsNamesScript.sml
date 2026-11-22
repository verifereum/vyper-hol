(* Linked runtime namespace and package-label facts. *)
Theory defaultDispatchModsNames
Ancestors
  alist list pair compileUnit compileVyper constSubstMods constSubst
  e2eModsDefs vyperTypeContract externalEntryChecks entryDispatchProps loweringShapeProps

Theorem source_typing_ok_mods_external_names_distinct:
  source_typing_ok_mods mods exps am tx /\ ALOOKUP mods src = SOME tops ==>
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops))
Proof
  rw[source_typing_ok_mods_def] >>
  metis_tac[ALOOKUP_MEM, check_contract_external_names_distinct,
            vyperTypeContractTheory.contract_keys_module_distinct]
QED

Theorem export_excludes_main_external:
  source_typing_ok_mods mods exps am tx /\ MEM name (MAP FST exps) ==>
  ~MEM (NONE:num option,name)
    (FLAT (MAP (external_name_keys_toplevel NONE) (main_module mods)))
Proof
  strip_tac >> CCONTR_TAC >> gvs[] >>
  Cases_on `ALOOKUP mods NONE` >>
  gvs[main_module_def,MEM_FLAT,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
  rename1 `MEM (NONE:num option,name) (external_name_keys_toplevel NONE top)` >>
  `MEM (NONE:num option,name) (self_member_keys_toplevel NONE top)` by
    (Cases_on `top` >> gvs[external_name_keys_toplevel_def,self_member_keys_toplevel_def]
     >~ [`FunctionDecl vis`] >- (Cases_on `vis` >> gvs[external_name_keys_toplevel_def])
     >~ [`VariableDecl kind`] >- (Cases_on `kind` >> gvs[external_name_keys_toplevel_def])
     >~ [`HashMapDecl kind`] >- (Cases_on `kind` >> gvs[external_name_keys_toplevel_def])) >>
  rename1 `MEM (name,src) exps` >>
  `MEM (NONE:num option,name) (contract_keys self_member_keys_toplevel mods)` by
    (drule ALOOKUP_MEM >> strip_tac >>
     rename1 `MEM (NONE,tops) mods` >>
     simp[contract_keys_def,MEM_FLAT,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
     map_every qexists_tac [`NONE`,`tops`,`top`] >> simp[]) >>
  fs[source_typing_ok_mods_def,EVERY_MEM,pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem exported_fn_name_list[local]:
  !src tops name.
  MAP (fn_decl_name o SND) (exported_fn src tops name) = [] \/
  MAP (fn_decl_name o SND) (exported_fn src tops name) = [name]
Proof
  rpt gen_tac >> simp[exported_fn_def] >> pairarg_tac >> gvs[] >>
  Cases_on `FILTER (\f. fn_decl_name f = name) exts` >> gvs[]
  >- (Cases_on `FILTER (\g. fn_decl_name g = name)
                  (FLAT (MAP (\t. case public_getter_src src t of
                                    NONE => [] | SOME g => [g]) tops))` >>
      gvs[FILTER_EQ_CONS]) >>
  gvs[FILTER_EQ_CONS]
QED

Theorem exported_labels[local]:
  !exps.
    (ALL_DISTINCT (MAP FST exps) ==>
     ALL_DISTINCT (MAP (\p. "fn_" ++ fn_decl_name (SND p)) (exported_fns mods exps))) /\
    (!name. MEM ("fn_" ++ name)
     (MAP (\p. "fn_" ++ fn_decl_name (SND p)) (exported_fns mods exps)) ==>
     MEM name (MAP FST exps))
Proof
  Induct >> simp[exported_fns_def] >>
  gen_tac >> PairCases_on `h` >>
  rename1 `exported_fns mods ((name,src)::exps)` >>
  Cases_on `ALOOKUP mods (SOME src)` >> gvs[exported_fns_def] >>
  rename1 `ALOOKUP mods (SOME src) = SOME tops` >>
  `MAP (\p. "fn_" ++ fn_decl_name (SND p)) (exported_fn (SOME src) tops name) =
   MAP (\n. "fn_" ++ n)
     (MAP (fn_decl_name o SND) (exported_fn (SOME src) tops name))` by
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
  qspecl_then [`SOME src`,`tops`,`name`] strip_assume_tac exported_fn_name_list >>
  gvs[MAP_APPEND] >> metis_tac[]
QED

Theorem linked_package_labels_distinct:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) ==>
  ALL_DISTINCT (MAP FST (MAP
    (set_external_package_target target o
     package_external_fn_unit mods T (K global_nonreentrant_slot)) exts))
Proof
  rpt strip_tac >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) (main_module mods)` >>
  PairCases_on `r` >>
  rename1 `FOLDR classify_function _ _ = (raws,_,_,_)` >>
  qabbrev_tac `main_fns = raws ++ public_getters (main_module mods)` >>
  `exts = MAP (\(src,f). (src,subst_consts_fn_mods (consts_env_mods mods) f))
               (exported_fns mods exps ++ MAP (\f. (NONE,f)) main_fns)` by
    (qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
     simp[classify_functions_unit_def,Abbr `main_fns`]) >>
  `!p. FST ((set_external_package_target target o
                package_external_fn_unit mods T (K global_nonreentrant_slot))
              ((\(src,f). (src,subst_consts_fn_mods (consts_env_mods mods) f)) p)) =
       "fn_" ++ fn_decl_name (SND p)` by
    simp[FORALL_PROD,combinTheory.o_DEF,package_external_fn_unit_def,
         set_external_package_target_def,subst_consts_fn_mods_def,fn_decl_name_def] >>
  `MAP FST (MAP (set_external_package_target target o
                 package_external_fn_unit mods T (K global_nonreentrant_slot)) exts) =
   MAP (\p. "fn_" ++ fn_decl_name (SND p)) (exported_fns mods exps) ++
   MAP (\f. "fn_" ++ fn_decl_name f) main_fns` by
    (fs[MAP_APPEND,MAP_MAP_o,combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `(NONE,x)` mp_tac) >> simp[combinTheory.o_DEF]) >>
  pop_assum SUBST1_TAC >> once_rewrite_tac[ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (mp_tac (Q.SPEC `exps` exported_labels) >>
      simp[] >> fs[source_typing_ok_mods_def]) >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) (main_module mods)))` by
    (Cases_on `ALOOKUP mods NONE` >> simp[main_module_def] >>
     metis_tac[source_typing_ok_mods_external_names_distinct]) >>
  conj_tac
  >- (drule classified_external_labels_distinct >>
      simp[classify_functions_def,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,
           subst_consts_fn_def,fn_decl_name_def,Abbr `main_fns`]) >>
  rpt strip_tac >>
  qpat_x_assum `MEM _ (MAP _ main_fns)` mp_tac >>
  simp[MEM_MAP,EXISTS_PROD,fn_decl_name_def] >> rpt strip_tac >> gvs[] >>
  drule (SIMP_RULE (srw_ss()) [] (cj 2 exported_labels)) >> strip_tac >>
  drule_all export_excludes_main_external >>
  gvs[Abbr `main_fns`,MEM_APPEND]
  >- (qspec_then `main_module mods` mp_tac classify_fold_external_source >>
      simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      goal_assum (drule_at Any) >> simp[external_name_keys_toplevel_def]) >>
  gvs[MEM_public_getters] >> drule public_getter_lookup_singleton >> strip_tac >>
  simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >> goal_assum (drule_at Any) >> simp[]
QED
