(* Recover the declaration supplying the grouped entry's nonempty defaults. *)
Theory linkedGroupedDefaultSource
Ancestors
  compileUnit compileVyper constSubstMods defaultDispatchModsGetter
  publicGetterProps vyperReadOnlySyntax loweringShapeProps vyperAST
  vyperTypeContract vyperTypeContractContext
  allocLimitsProps compileEnv finite_map list pair alist rich_list

val _ = Parse.hide "tops";
val _ = Parse.hide "body";

Theorem classified_external_default_source_mods:
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  MEM (src,(mut,nr,rr,name,args,ds,ret,body)) exts /\ ds <> [] ==>
  ?tops defaults stmts.
    ALOOKUP mods src = SOME tops /\
    MEM (FunctionDecl External mut nr rr name args defaults ret stmts) tops /\
    subst_consts_fn_mods (consts_env_mods mods)
      (mut,nr,rr,name,args,defaults,ret,stmts) =
      (mut,nr,rr,name,args,ds,ret,body)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [classify_functions_unit_def, LET_THM, Excl "MAP_APPEND"] >>
  pairarg_tac >> simp[Excl "MAP_APPEND"] >>
  strip_tac >>
  qpat_x_assum `MEM (src,_) exts` mp_tac >>
  qpat_assum `MAP _ _ = exts` (SUBST1_TAC o SYM) >>
  PURE_REWRITE_TAC [MEM_MAP] >>
  disch_then (qx_choose_then `source` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  Cases_on `source` >>
  rename1 `MEM (source_id,original) (_ ++ _)` >> PairCases_on `original` >>
  qpat_x_assum `(src,_) = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [pairTheory.UNCURRY] o SYM) >>
  qpat_x_assum `source_id = src` SUBST_ALL_TAC >>
  rename1 `subst_consts_fn_mods _ (mu,nrr,raw_rr,fnm,fargs,raw_defaults,rt,raw_body) = _` >>
  `raw_defaults <> []` by
    (strip_tac >> fs[subst_consts_fn_mods_def, subst_consts_expr_mods_def]) >>
  `?tls.
     ALOOKUP mods src = SOME tls /\
     MEM (FunctionDecl External mu nrr raw_rr fnm fargs raw_defaults rt raw_body) tls` by
    (qpat_x_assum `MEM (src,_) (_ ++ _)` (mp_tac o REWRITE_RULE [MEM_APPEND]) >>
     disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
     >- (qsuff_tac `!exports.
          MEM (src,(mu,nrr,raw_rr,fnm,fargs,raw_defaults,rt,raw_body))
            (exported_fns mods exports) ==>
          ?tls. ALOOKUP mods src = SOME tls /\
            MEM (FunctionDecl External mu nrr raw_rr fnm fargs raw_defaults rt raw_body) tls`
         >- (disch_then (qspec_then `exps` drule) >> simp[]) >>
         Induct >> simp[exported_fns_def] >> qx_gen_tac `export` >> PairCases_on `export` >>
         Cases_on `ALOOKUP mods (SOME export1)` >> simp[exported_fns_def, MEM_APPEND] >>
         rename1 `ALOOKUP mods (SOME export1) = SOME imported_tops` >>
         disch_then (DISJ_CASES_THEN2 mp_tac (fn tail =>
           qpat_assum `MEM _ (exported_fns mods exports) ==> _`
             (ACCEPT_TAC o C MATCH_MP tail))) >>
         simp[exported_fn_def] >> pairarg_tac >> simp[] >>
         rename1 `FOLDR classify_function _ _ = (fold_exts,fold_ints,fold_fb,fold_ctor)` >>
         Cases_on `FILTER (\f. fn_decl_name f = export0) fold_exts` >> simp[]
         >- (Cases_on `FILTER (\g. fn_decl_name g = export0)
                (FLAT (MAP (\t. case public_getter_src (SOME export1) t of
                            NONE => [] | SOME g => [g]) imported_tops))` >>
             simp[] >> strip_tac >> gvs[] >>
             qpat_assum `FILTER _ _ = _::_`
               (mp_tac o Q.AP_TERM `MEM (mu,nrr,raw_rr,fnm,fargs,raw_defaults,rt,raw_body)`) >>
             simp[MEM_FILTER,MEM_FLAT,MEM_MAP,AllCaseEqs(),PULL_EXISTS] >>
             rpt strip_tac >> gvs[] >>
             drule (iffLR (SPEC_ALL tagged_getter_source_tuple)) >> strip_tac >>
             drule external_getter_defaults >> simp[]) >>
         strip_tac >> gvs[] >>
         qpat_assum `FILTER _ _ = _::_`
           (mp_tac o Q.AP_TERM `MEM (mu,nrr,raw_rr,fnm,fargs,raw_defaults,rt,raw_body)`) >>
         simp[MEM_FILTER] >> strip_tac >>
         irule classify_fold_external_source >> simp[]) >>
     simp[MEM_MAP,MEM_APPEND] >> strip_tac >> gvs[]
     >- (Cases_on `ALOOKUP mods NONE` >> gvs[main_module_def] >>
         irule classify_fold_external_source >> simp[]) >>
     fs[MEM_public_getters] >> drule public_getter_defaults >> simp[]) >>
  qexistsl_tac [`tls`,`raw_defaults`,`raw_body`] >>
  gvs[subst_consts_fn_mods_def]
QED

Theorem classified_external_owner_allocated_mods:
  check_contract F layouts addr mods = SOME art /\
  exports_ok layouts addr mods exps /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  MEM (src,fn) exts /\ ALOOKUP mods src = SOME tops ==>
  module_allocated layouts addr src tops
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `src`
  >- (drule_all_then ACCEPT_TAC check_contract_main_module_allocated) >>
  rename1 `ALOOKUP mods (SOME owner) = SOME tops` >>
  `?original. MEM (SOME owner,original) (exported_fns mods exps)` by
    (qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [classify_functions_unit_def, LET_THM, Excl "MAP_APPEND"] >>
     pairarg_tac >> simp[Excl "MAP_APPEND"] >> strip_tac >>
     qpat_x_assum `MEM (SOME owner,fn) exts` mp_tac >>
     qpat_assum `MAP _ _ = exts` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP, MEM_APPEND, PULL_EXISTS, FORALL_PROD] >>
     metis_tac[]) >>
  `!s tls key srcfn f. MEM (srcfn,f) (exported_fn s tls key) ==> srcfn = s` by
    (rpt gen_tac >> simp[exported_fn_def] >>
     pairarg_tac >> simp[] >> BasicProvers.every_case_tac >> simp[]) >>
  `!exports original.
    MEM (SOME owner,original) (exported_fns mods exports) ==>
    ?key. MEM (key,owner) exports` by
    (Induct >> simp[exported_fns_def] >>
     qx_gen_tac `export` >> PairCases_on `export` >>
     gen_tac >> Cases_on `ALOOKUP mods (SOME export1)` >>
     simp[exported_fns_def, MEM_APPEND] >>
     rpt strip_tac
     >- (qpat_assum `!f. MEM _ (exported_fns mods exports) ==> _`
           (drule_then (qx_choose_then `key` assume_tac)) >>
         qexists_tac `key` >> simp[])
     >- (qexists_tac `export0` >>
         qpat_assum `MEM _ (exported_fn _ _ _)` mp_tac >>
         qpat_assum `!s tls key srcfn f. _` (fn th =>
           disch_then (mp_tac o MATCH_MP (SPEC_ALL th))) >>
         simp[]) >>
     qpat_assum `!f. MEM _ (exported_fns mods exports) ==> _`
       (drule_then (qx_choose_then `key` assume_tac)) >>
     qexists_tac `key` >> simp[]) >>
  qpat_assum `!exports f. MEM _ (exported_fns _ _) ==> _`
    (qspec_then `exps` drule) >> strip_tac >>
  qpat_assum `exports_ok layouts addr mods exps`
    (qspec_then `(key,owner)` mp_tac o REWRITE_RULE [EVERY_MEM] o
     CONJUNCT1 o PURE_REWRITE_RULE [exports_ok_def]) >>
  simp[]
QED

Theorem classified_grouped_default_compile_inputs_mods:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  EXISTS (external_has_defaults o SND) exts /\
  MEM (src,(mut,nr,rr,name,args,ds,ret,body)) exts /\
  package_external_group_unit mods rp.rpol_target T
    (K global_nonreentrant_slot) (src,(mut,nr,rr,name,args,ds,ret,body)) =
      ExternalDefaults common entries specs off ==>
  ds <> [] /\
  specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH ds) args,ds)) /\
  fn_allocs_ok_unit mods (src,(mut,nr,rr,name,args,ds,ret,body)) /\
  no_sha256_exprs ds /\
  alloc_limits_exprs (common.ec_env with ce_vars := FEMPTY) ds
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_allocs_ok_unit mods (src,(mut,nr,rr,name,args,ds,ret,body)) /\
   no_sha256_exprs ds` by
    (qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
     qpat_assum `classify_functions_unit _ _ = _` (fn classified =>
       qpat_assum `EXISTS _ exts` (fn grouped =>
         simp_tac bool_ss [lower_vyper_runtime_unit_mods_def, LET_THM,
           classified, grouped, pairTheory.ELIM_UNCURRY])) >>
     IF_CASES_TAC >> simp[] >> strip_tac >>
     qpat_x_assum `compute_immutables_len_unit _ _ < _ /\ _`
       (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [EVERY_APPEND]) >>
     qpat_assum `EVERY (fn_allocs_ok_unit _) exts`
       (drule_then assume_tac o REWRITE_RULE [EVERY_MEM]) >>
     qpat_assum `EVERY (external_defaults_no_sha256 o SND) exts`
       (drule_then mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[external_defaults_no_sha256_def]) >>
  qabbrev_tac `allocation_env =
    build_compile_env_unit mods src Internal mut name args ret body F` >>
  `alloc_limits_exprs allocation_env ds` by
    fs[fn_allocs_ok_unit_def, Abbr `allocation_env`] >>
  qabbrev_tac `entry_env =
    build_compile_env_unit mods src External mut name args ret body T` >>
  `ds <> [] /\
   specs = MAP (\((n,ty),e). (n,ty,e))
     (ZIP (DROP (LENGTH args - LENGTH ds) args,ds)) /\
   (common.ec_env with ce_vars := FEMPTY).ce_struct_fields =
     entry_env.ce_struct_fields /\
   (common.ec_env with ce_vars := FEMPTY).ce_func_return_type =
     entry_env.ce_func_return_type /\
   (common.ec_env with ce_vars := FEMPTY).ce_modules =
     entry_env.ce_modules /\
   (common.ec_env with ce_vars := FEMPTY).ce_var_type =
     entry_env.ce_var_type /\
   (common.ec_env with ce_vars := FEMPTY).ce_hashmap_info =
     entry_env.ce_hashmap_info /\
   (common.ec_env with ce_vars := FEMPTY).ce_module_var_type =
     entry_env.ce_module_var_type /\
   (common.ec_env with ce_vars := FEMPTY).ce_module_vars =
     entry_env.ce_module_vars` by
    (qpat_x_assum `package_external_group_unit _ _ _ _ _ = _` mp_tac >>
     Cases_on `ds` >> Cases_on `ret = NoneT` >>
     simp[package_external_group_unit_def, package_external_fn_unit_def,
          set_external_package_target_def, update_cenv_nonreentrant_def,
          update_cenv_ret_abi_def, GSYM markerTheory.Abbrev_def, AllCaseEqs()] >>
     strip_tac >> gvs[]) >>
  simp[] >>
  `alloc_limits_exprs (common.ec_env with ce_vars := FEMPTY) =
   alloc_limits_exprs allocation_env` suffices_by simp[] >>
  irule (cj 4 (UNDISCH (SPEC_ALL alloc_limits_frame)) |> DISCH_ALL) >>
  asm_rewrite_tac[] >>
  simp[Abbr `entry_env`, Abbr `allocation_env`, build_compile_env_unit_def] >>
  rpt (pairarg_tac >> simp[])
QED
