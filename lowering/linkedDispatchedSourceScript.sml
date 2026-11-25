(* Recover the exact source lookup from successful default-free dispatch. *)
Theory linkedDispatchedSource
Ancestors
  dispatchedSignatureMemberMods dispatchedSignatureOriginMods
  defaultDispatchModsFallback defaultDispatchModsGetter defaultDispatchModsNames
  entryDispatchProps e2eModsDefs compileVyper compileUnit loweringShapeProps
  vyperTypeContract vyperTypeContractContext vyperTypeContractGetter
  vyperInterpreter vyperCalldata vyperABIEntries venomInst alist list pair
  runtimeFallbackSourceAlignment constSubst

val _ = Parse.hide "body";

Theorem lookup_function_external_unique_tagged_decl:
  !tops top src name result.
    ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops)) /\
    MEM top tops /\
    MEM (src,name) (external_name_keys_toplevel src top) /\
    vyperInterpreter$lookup_function src name External [top] = SOME result ==>
    vyperInterpreter$lookup_function src name External tops = SOME result
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `top = h` >> gvs[]
  >- (Cases_on `h` >>
      gvs[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def]
      >>~- ([`FunctionDecl vis _ _ _ _ _ _ _ _`],
        Cases_on `vis` >> gvs[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def])
      >>~- ([`VariableDecl kind _ _ _ _`],
        Cases_on `kind` >> gvs[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def])
      >>~- ([`HashMapDecl kind _ _ _ _ _`],
        Cases_on `kind` >> gvs[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def])) >>
  `~MEM (src,name) (external_name_keys_toplevel src h)` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     strip_tac >>
     CCONTR_TAC >> fs[] >>
     qpat_assum `!e. MEM e (external_name_keys_toplevel src h) ==> _`
       (qspec_then `(src,name)` (fn distinct =>
         qpat_assum `MEM (src,name) (external_name_keys_toplevel src h)`
           (mp_tac o Q.SPEC `top` o MP distinct))) >> simp[]) >>
  `~MEM (NONE:num option,name)
    (external_name_keys_toplevel (NONE:num option) h)` by
    (Cases_on `h` >> gvs[external_name_keys_toplevel_def]
     >>~- ([`FunctionDecl vis _ _ _ _ _ _ _ _`],
       Cases_on `vis` >> gvs[external_name_keys_toplevel_def])
     >>~- ([`VariableDecl kind _ _ _ _`],
       Cases_on `kind` >> gvs[external_name_keys_toplevel_def])
     >>~- ([`HashMapDecl kind _ _ _ _ _`],
       Cases_on `kind` >> gvs[external_name_keys_toplevel_def])) >>
  simp[lookup_function_external_skip] >>
  qpat_x_assum `!top src name result. _` irule >>
  gvs[ALL_DISTINCT_APPEND] >> qexists_tac `top` >> simp[]
QED

Theorem linked_fallback_source_entry_mods:
  source_typing_ok_mods mods exps am tx /\
  (list$EXISTS is_default_decl (main_module mods) \/
   IS_SOME (exported_fallback mods exps)) ==>
  ?tops mut nr ret fbody.
    ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops /\
    vyperInterpreter$lookup_function (ALOOKUP exps "__default__") "__default__"
      External tops = SOME (mut,nr,[],[],ret,fbody)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?tops mut nr rr args ds ret body.
    ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops /\
    MEM (FunctionDecl External mut nr rr "__default__" args ds ret body) tops` by
    (qpat_x_assum `list$EXISTS is_default_decl (main_module mods) \/ _`
       (DISJ_CASES_THEN assume_tac)
     >- (Cases_on `ALOOKUP mods NONE` >> fs[main_module_def] >>
         rename1 `ALOOKUP mods NONE = SOME main` >>
         qpat_x_assum `list$EXISTS is_default_decl main`
           (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
         rename1 `is_default_decl decl` >> Cases_on `decl` >>
         fs[is_default_decl_def] >> Cases_on `f` >> fs[is_default_decl_def] >>
         `ALOOKUP exps "__default__" = NONE` by
           (simp[ALOOKUP_NONE] >> strip_tac >>
            mp_tac (Q.INST [`name` |-> `"__default__"`]
              export_excludes_main_external) >>
            impl_tac >- asm_rewrite_tac[] >>
            simp[main_module_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
            goal_assum (drule_at Any) >> simp[external_name_keys_toplevel_def]) >>
         asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[]) >>
     Cases_on `exported_fallback mods exps` >> fs[] >>
     PairCases_on `x` >>
     rename1 `exported_fallback mods exps = SOME (owner,decl)` >>
     drule_then (qx_choosel_then [`n`,`tops`] strip_assume_tac) exported_fallback_slot >>
     qpat_x_assum `owner = SOME n` SUBST_ALL_TAC >>
     `ALL_DISTINCT (MAP FST exps)` by
       (fs[source_typing_ok_mods_def] >> drule_then strip_assume_tac exports_ok_names >>
        FIRST_ASSUM ACCEPT_TAC) >>
     `ALOOKUP exps "__default__" = SOME n` by
       metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
     PairCases_on `decl` >>
     rename1 `FST (SND (SND (FOLDR classify_function _ tops))) =
       SOME (mut,nr,rr,fn,args,ds,ret,body)` >>
     `fn = "__default__"` by
       (`FST (SND (SND (classify_functions tops))) =
           SOME (mut,nr,rr,fn,args,subst_consts_exprs (module_consts_env tops []) ds,
             ret,subst_consts_stmts (module_consts_env tops []) body)` by
         (Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
          PairCases_on `r` >> gvs[classify_functions_def, subst_consts_fn_def]) >>
        drule_then ACCEPT_TAC classified_fallback_name) >>
     qpat_x_assum `fn = "__default__"` SUBST_ALL_TAC >>
     drule classify_fold_fallback_mem >> strip_tac >>
     qexists_tac `tops` >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all_then assume_tac source_typing_ok_mods_external_names_distinct >>
  qpat_assum `source_typing_ok_mods _ _ _ _`
    (qx_choose_then `art` (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE [source_typing_ok_mods_def]) >>
  `MEM (ALOOKUP exps "__default__",tops) mods` by
    drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `module_allocated am.layouts tx.target (ALOOKUP exps "__default__") tops` by
    (Cases_on `ALOOKUP exps "__default__"` >> fs[] >>
     FIRST [drule_all_then ACCEPT_TAC check_contract_main_module_allocated,
       rename1 `ALOOKUP exps "__default__" = SOME owner` >>
       `MEM ("__default__",owner) exps` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
       qpat_assum `exports_ok _ _ _ _`
         (qspec_then `("__default__",owner)` mp_tac o
          REWRITE_RULE [EVERY_MEM] o CONJUNCT1 o REWRITE_RULE [exports_ok_def]) >>
       simp[]]) >>
  `args = []` by
    (drule_all check_contract_function_header >>
     Cases_on `args` >> simp[function_header_ok_def]) >>
  `ds = []` by
    (drule_all (SIMP_RULE (srw_ss()) []
        (Q.INST [`vis` |-> `External`] check_contract_runtime_function_body_MEM)) >>
     simp[check_function_body_def, LET_THM]) >>
  qexistsl_tac [`tops`,`mut`,`nr`,`ret`,`body`] >> simp[] >>
  irule lookup_function_external_unique_tagged_decl >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[external_name_keys_toplevel_def, vyperInterpreterTheory.lookup_function_def]
QED

Theorem calldata_dispatch_linear_has_source_entry_mods:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  ~EXISTS (external_has_defaults o SND) exts /\
  calldata_dispatch_mods mods exps cd = SOME (name,vals) ==>
  ?tops mut nr args ret fbody.
    ALOOKUP mods (ALOOKUP exps name) = SOME tops /\
    vyperInterpreter$lookup_function (ALOOKUP exps name) name External tops =
      SOME (mut,nr,args,[],ret,fbody)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `if LENGTH cd < 4 then NONE else
    FIND (\(n,tys). abi_method_id (type_env_all_modules mods) n tys = cd_selector cd)
      (abi_deployed_signatures mods exps)`
  >- suspend "source_fallback" >>
  PairCases_on `x` >>
  rename1 `(if LENGTH cd < 4 then NONE else _) = SOME (hit_name,tys)` >>
  qpat_x_assum `calldata_dispatch_mods _ _ _ = _` (fn dispatch =>
    qpat_assum `(if LENGTH cd < 4 then NONE else _) = _` (fn hit =>
      mp_tac (REWRITE_RULE [calldata_dispatch_mods_def, LET_THM, hit] dispatch))) >>
  simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `MEM (hit_name,tys) (abi_deployed_signatures mods exps)` by
    (Cases_on `LENGTH cd < 4` >> fs[] >>
     drule_then ACCEPT_TAC FIND_MEM) >>
  `~EXISTS (external_has_defaults o SND) exts` by fs[] >>
  drule_all deployed_default_free_signature_member >>
  disch_then (qx_choosel_then [`tops`,`top`,`mut`,`nr`,`rr`,`args`,`ret`,`body`]
    strip_assume_tac) >>
  drule_all_then assume_tac source_typing_ok_mods_external_names_distinct >>
  qexistsl_tac [`tops`,`mut`,`nr`,`args`,`ret`,`body`] >> simp[] >>
  irule lookup_function_external_unique_tagged_decl >> simp[]
  >- (qexists_tac `top` >> simp[vyperInterpreterTheory.lookup_function_def,
        external_name_keys_toplevel_def]) >>
  qexists_tac `top` >> simp[] >>
  `MEM (ALOOKUP exps hit_name,hit_name) (external_name_keys_toplevel (ALOOKUP exps hit_name) top)` by
    (drule tagged_getter_name_key >> simp[fn_decl_name_def]) >>
  drule (iffLR (SPEC_ALL tagged_getter_source_tuple)) >> strip_tac >>
  Cases_on `top` >> gvs[is_public_getter_decl_def]
  >- (Cases_on `v` >> gvs[is_public_getter_decl_def,
         external_getter_tuple_def, vyperInterpreterTheory.lookup_function_def]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def,
    external_getter_tuple_def, vyperInterpreterTheory.lookup_function_def]
QED

Resume calldata_dispatch_linear_has_source_entry_mods[source_fallback]:
  `name = "__default__"` by
    (qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE` (fn miss =>
       qpat_assum `calldata_dispatch_mods _ _ _ = _`
         (mp_tac o PURE_REWRITE_RULE [calldata_dispatch_mods_def, LET_THM, miss])) >>
     COND_CASES_TAC >> simp[]) >>
  qpat_x_assum `name = "__default__"` SUBST_ALL_TAC >>
  Q.SUBGOAL_THEN
    `list$EXISTS is_default_decl (main_module mods) \/ IS_SOME (exported_fallback mods exps)`
    assume_tac
  >- (qpat_assum `(if LENGTH cd < 4 then NONE else _) = NONE` (fn miss =>
        qpat_assum `calldata_dispatch_mods _ _ _ = _`
          (mp_tac o PURE_REWRITE_RULE [calldata_dispatch_mods_def, LET_THM, miss])) >>
      COND_CASES_TAC >> simp[]) >>
  drule_all linked_fallback_source_entry_mods >>
  disch_then (qx_choosel_then [`tops`,`mut`,`nr`,`ret`,`fbody`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`tops`,`mut`,`nr`,`[]`,`ret`,`fbody`] >> simp[]
QED

Finalise calldata_dispatch_linear_has_source_entry_mods
