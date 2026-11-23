Theory whitelistLinkedBodyProps
Ancestors
  alist list pair supportedExprs supportedTypes vyperTypeContractContext e2eDefs supportedProgram vyperAST vyperTypeContract
  vyperImportRefs vyperImportRefsProps vyperTypeContractStaticMaps
  whitelistCheckerDecls whitelistLinkedBodyEnv whitelistLinkedBodyRange
  whitelistLinkedBodyData whitelistLinkedBodyCalls whitelistLinkedBodyExprs
  whitelistLinkedBodyStmtForms whitelistLinkedBodyStmts whitelistLinkedBodyTypes
Triviality linked_checked_body_supported:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  am.layouts = layouts /\ tx.target = addr /\
  (src = NONE ==> layouts_agree tops am tx) /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  (mode ==> vis = Deploy) /\
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss ==>
  supported_function_body tops vis args ss /\
  (vis <> Deploy ==> EVERY (supported_pure_expr tops) dflts)
Proof
  strip_tac >>
  `MEM (src,tops) mods` by metis_tac[ALOOKUP_MEM] >>
  `src <> NONE ==> imported_stmts_refs_ok ss /\ imported_exprs_refs_ok dflts` by
    (Cases_on `src` >> simp[] >> strip_tac >>
     drule_all check_contract_imported_toplevel_refs_ok >>
     simp[EVERY_MEM] >>
     disch_then (qspec_then `FunctionDecl vis mut nr rr name args dflts ret ss` mp_tac) >>
     simp[imported_toplevel_refs_ok_def]) >>
  `src = NONE ==> !name. ~MEM (StructDecl name []) tops` by
    (strip_tac >> gen_tac >> strip_tac >> gvs[] >>
     qpat_x_assum `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) tops` kall_tac >>
     drule_all check_contract_toplevel_decl_MEM_checked >>
     simp[check_toplevel_decl_def]) >>
  `linked_body_type_facts tops src (type_env_all_modules mods)` by
    metis_tac[linked_checked_body_type_facts] >>
  qabbrev_tac `env = function_entry_env art mods src vis args` >>
  qabbrev_tac `ss_sub = subst_consts_stmts_mods (consts_env_mods mods) ss` >>
  `env.type_defs = type_env_all_modules mods /\
   env.bare_globals = art.cta_bare_globals /\
   env.bare_global_assignable = art.cta_bare_global_assignable /\
   env.toplevel_vtypes = art.cta_toplevel_vtypes /\
   env.event_fields = art.cta_event_fields` by
    simp[Abbr `env`, function_entry_env_def, artifact_env_def,
         vyperTypeContractContextTheory.FOLDL_extend_local_args_static] >>
  `src = NONE ==> !ty. assignable_type (type_env_all_modules mods) ty ==>
        supported_place_type tops ty` by
    (strip_tac >> fs[linked_body_type_facts_def] >> metis_tac[]) >>
  `linked_body_data_env tops src env` by
    metis_tac[linked_checked_data_env] >>
  `?fs. (~mode \/ src <> NONE ==> fs = env.fn_sigs) /\
        linked_body_calls_env tops src (env with fn_sigs := fs) /\
        IS_SOME (type_stmts (env with fn_sigs := fs) ret ss) /\
        IS_SOME (type_stmts (env with fn_sigs := fs) ret ss_sub)` by
    metis_tac[linked_checked_body_calls] >>
  qabbrev_tac `env_fs = env with fn_sigs := fs` >>
  `linked_body_data_env tops src env_fs` by
    (fs[Abbr `env_fs`, linked_body_data_env_def] >> metis_tac[]) >>
  `params_ok (type_env_all_modules mods) args` by
    (qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [check_function_body_def]) >>
     simp[Abbr `env`, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `!x ty. FLOOKUP env.var_types x = SOME ty ==>
      assignable_type (type_env_all_modules mods) ty` by
    (rpt gen_tac >> strip_tac >>
     `ALL_DISTINCT (MAP FST args)` by metis_tac[params_ok_def] >>
     qpat_x_assum `ALL_DISTINCT (MAP FST args)` kall_tac >>
     pop_assum mp_tac >>
     simp[Abbr `env`, function_entry_env_def] >> strip_tac >>
     `ALL_DISTINCT (MAP FST args)` by metis_tac[params_ok_def] >>
     `MEM (x,ty) args` by
       (qspecl_then [`args`, `artifact_env art mods src`, `x`, `ty`] mp_tac
          (Q.INST [`asg` |-> `vis = Internal`]
           vyperTypeContractContextTheory.FOLDL_extend_local_args_var_types_range) >>
        gvs[vyperTypeContractTheory.artifact_env_def]) >>
     qpat_x_assum `params_ok _ _` (mp_tac o REWRITE_RULE [params_ok_def]) >>
     simp[EVERY_MEM] >> strip_tac >>
     first_x_assum (qspec_then `(x,ty)` mp_tac) >> simp[]) >>
  `FDOM env_fs.var_types = set (MAP FST args)` by
    simp[Abbr `env_fs`, Abbr `env`, function_entry_env_var_types_fdom] >>
  `ALL_DISTINCT (MAP FST args)` by metis_tac[params_ok_def] >>
  `?out. type_stmts env_fs ret ss = SOME out` by
    (gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `custom_errors_stmts_ok mods ss` by
    (qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [check_function_body_def]) >>
     simp[Abbr `env`, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `!k ty. FLOOKUP env_fs.bare_global_assignable k = SOME ty ==>
      FLOOKUP env_fs.bare_globals k = SOME ty` by
    (rpt gen_tac >> strip_tac >> Cases_on `mode`
     >- (drule (Q.INST [`sources` |-> `[(addr,mods)]`,
                         `tx` |-> `(empty_call_txn with target := addr)`]
                  vyperTypeContractStaticMapsTheory.check_contract_bare_global_assignable_consistent_deploy) >>
         fs[Abbr `env_fs`, Abbr `env`] >> strip_tac >>
         first_x_assum (qspecl_then [`FST k`, `SND k`, `ty`] mp_tac) >>
         simp[] >> strip_tac >>
         metis_tac[pairTheory.pair_CASES])
     >- (drule (Q.INST [`sources` |-> `[(addr,mods)]`,
                         `tx` |-> `(empty_call_txn with target := addr)`]
                  vyperTypeContractStaticMapsTheory.check_contract_bare_global_assignable_consistent_initial) >>
         fs[Abbr `env_fs`, Abbr `env`] >> strip_tac >>
         first_x_assum (qspecl_then [`FST k`, `SND k`, `ty`] mp_tac) >>
         simp[] >> strip_tac >>
         metis_tac[pairTheory.pair_CASES])) >>
  `linked_body_env tops src (type_env_all_modules mods) env_fs` by
    (simp[linked_body_env_def, Abbr `env_fs`] >> metis_tac[]) >>
  `!env0 e. linked_body_env tops src (type_env_all_modules mods) env0 /\
      (src = NONE \/ imported_expr_refs_ok e) /\ well_typed_expr env0 e ==>
      supported_pure_expr tops e` by
    (rpt gen_tac >> strip_tac >>
     metis_tac[linked_well_typed_expr_supported]) >>
  `type_stmts env_fs ret ss = SOME (THE (type_stmts env_fs ret ss))` by
    gvs[optionTheory.IS_SOME_EXISTS] >>
  `!env0 ret0 x ty0 a b n lbody out0 ta i tb j.
      (src = NONE \/ imported_expr_refs_ok a /\ imported_expr_refs_ok b) /\
      type_stmt env0 ret0 (For x ty0 (Range a b) n lbody) = SOME out0 /\
      IS_SOME (type_stmt env0 ret0
        (subst_consts_stmt_mods (consts_env_mods mods)
          (For x ty0 (Range a b) n lbody))) /\
      subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
      subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j) ==>
      i <= j /\ n = Num (j - i)` by
    (rpt gen_tac >>
     rewrite_tac[constSubstModsTheory.subst_consts_stmt_mods_def,
                 constSubstModsTheory.subst_consts_iter_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all linked_checked_range_literals >> simp[]) >>
  `!env0 ret0 s out0.
      linked_body_env tops src (type_env_all_modules mods) env0 /\
      (src = NONE \/ imported_stmt_refs_ok s) /\
      FDOM env0.var_types SUBSET
        set (MAP FST (args ++ supported_stmts_bindings T ss ++
                      supported_stmts_bindings F ss)) /\
      custom_errors_stmt_ok mods s /\
      type_stmt env0 ret0 s = SOME out0 /\
      (!c yes no. s <> If c yes no) /\
      (!x ty0 it n b. s <> For x ty0 it n b) ==>
      supported_stmt tops
        (args ++ supported_stmts_bindings T ss ++
         supported_stmts_bindings F ss) s` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule linked_stmt_leaf_supported >> simp[] >>
     qexistsl_tac [`env0`, `out0`, `mods`, `ret0`, `src`,
                   `type_env_all_modules mods`] >>
     simp[] >>
     rpt conj_tac
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         drule linked_well_typed_expr_supported >>
         disch_then (qspec_then `type_env_all_modules mods`
           (map_every assume_tac o CONJUNCTS)) >>
         qpat_assum `!env tgt. IS_SOME (type_place_target env tgt) ==> _`
           (qspecl_then [`env0`, `bt`] mp_tac) >> simp[])
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `!en e. linked_body_env _ _ _ en /\ _ ==> supported_pure_expr _ e`
           (qspecl_then [`env0`, `e`] mp_tac) >> simp[])
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         drule linked_well_typed_expr_supported >>
         disch_then (qspec_then `type_env_all_modules mods`
           (map_every assume_tac o CONJUNCTS)) >>
         qpat_assum `!env es. well_typed_exprs env es ==> _`
           (qspecl_then [`env0`, `es`] mp_tac) >> simp[]) >>
     fs[linked_body_env_def]) >>
  conj_tac
  >- (irule (Q.INST [`tops` |-> `tops`, `args` |-> `args`, `ss` |-> `ss`,
                 `env` |-> `env_fs`, `mods` |-> `mods`,
                 `out` |-> `THE (type_stmts env_fs ret ss)`, `ret` |-> `ret`,
                 `src` |-> `src`, `tenv` |-> `type_env_all_modules mods`]
                (INST_TYPE [``:'a`` |-> ``:num``]
                  linked_typed_body_supported)) >>
  conj_tac
  >- metis_tac[params_ok_def]
  >- (qexists `env_fs` >> qexists `mods` >>
      qexists `ret` >> qexists `src` >>
      simp[Abbr `ss_sub`] >>
      rpt conj_tac >> rpt strip_tac >> res_tac >> simp[] >>
      Cases_on `src` >> simp[] >>
      qpat_assum `_ <> NONE ==> imported_stmts_refs_ok ss /\ _` mp_tac >> simp[])) >>
  strip_tac >>
  `~mode` by metis_tac[] >>
  `env_fs = env` by
    (simp[Abbr `env_fs`] >> metis_tac[]) >>
  `linked_body_env tops src (type_env_all_modules mods) (defaults_env env)` by
    metis_tac[linked_body_env_defaults] >>
  `well_typed_exprs (defaults_env env) dflts` by
    (qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [check_function_body_def]) >>
     simp[Abbr `env`]) >>
  drule linked_well_typed_expr_supported >>
  disch_then (qspec_then `type_env_all_modules mods`
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!env es. well_typed_exprs env es ==> _`
    (qspecl_then [`defaults_env env`, `dflts`] mp_tac) >>
  simp[] >> Cases_on `src` >> simp[] >>
  qpat_assum `_ <> NONE ==> imported_stmts_refs_ok ss /\ _` mp_tac >> simp[]
QED

Theorem check_contract_linked_supported_function_body:
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  am.layouts = cx.layouts /\
  ALOOKUP mods src = SOME tops /\
  (src = NONE ==> layouts_agree tops am cx.txn) /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  (src = NONE \/ context_function_live cx (src,name)) ==>
  supported_declaration_body tops (FunctionDecl vis mut nr rr name args dflts ret ss) /\
  (cx.in_deploy ==> supported_deploy_declaration tops
    (FunctionDecl vis mut nr rr name args dflts ret ss))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!mode a. check_contract mode cx.layouts cx.txn.target mods = SOME a /\
    (mode ==> vis = Deploy) /\
    check_function_body cx.layouts cx.txn.target mods a src vis mut nr args dflts ret ss ==>
    supported_function_body tops vis args ss /\
    (vis <> Deploy ==> EVERY (supported_pure_expr tops) dflts)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`layouts` |-> `(cx:evaluation_context).layouts`, `addr` |-> `cx.txn.target`,
                    `tx` |-> `cx.txn`, `art` |-> `a`]
                   linked_checked_body_supported) >> simp[]) >>
  `function_live cx.layouts cx.txn.target mods
     (live_functions cx.layouts cx.txn.target mods) (src,name)` by
    (Cases_on `src`
     >- (irule module_allocated_function_live >> qexists_tac `tops` >> simp[] >>
         irule check_contract_main_module_allocated >>
         qexistsl_tac [`runtime_art`, `F`, `mods`] >> simp[]) >>
     qpat_assum `_ = NONE \/ context_function_live _ _` mp_tac >>
     qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods`
       (fn eq => rewrite_tac[context_function_live_def, eq]) >> simp[]) >>
  Cases_on `vis = Deploy`
  >- (qpat_x_assum `vis = Deploy` SUBST_ALL_TAC >>
      simp[supported_declaration_body_def, supported_deploy_declaration_def] >>
      strip_tac >>
      `check_contract T cx.layouts cx.txn.target mods = SOME art` by fs[] >>
      `check_function_body cx.layouts cx.txn.target mods art src Deploy mut nr args dflts ret ss` by
        (irule check_contract_live_deploy_function_body_MEM >> simp[] >>
         qexistsl_tac [`name`, `rr`] >> simp[]) >>
      `supported_function_body tops Deploy args ss` by
        (qpat_assum `!mode a. _` (qspecl_then [`T`, `art`] mp_tac) >> simp[]) >>
      simp[supported_value_type_def, EVERY_MEM, FORALL_PROD] >>
      rpt gen_tac >> strip_tac >>
      rename1 `MEM (arg,ty) args` >>
      `assignable_type (type_env_all_modules mods) ty` by
        (qpat_x_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[check_function_body_def, params_ok_def, EVERY_MEM, FORALL_PROD] >>
         metis_tac[]) >>
      `src = NONE \/ imported_type_refs_ok ty` by
        (Cases_on `src` >> simp[] >>
         `MEM (SOME x,tops) mods` by metis_tac[ALOOKUP_MEM] >>
         drule_all check_contract_imported_toplevel_refs_ok >>
         simp[EVERY_MEM] >>
         disch_then (qspec_then `FunctionDecl Deploy mut nr rr name args dflts ret ss` mp_tac) >>
         simp[imported_toplevel_refs_ok_def, EVERY_MEM, FORALL_PROD] >>
         metis_tac[]) >>
      `linked_body_type_facts tops src (type_env_all_modules mods)` by
        metis_tac[linked_checked_body_type_facts] >>
      fs[linked_body_type_facts_def]) >>
  `check_function_body cx.layouts cx.txn.target mods runtime_art src vis mut nr args dflts ret ss` by
    (irule check_contract_function_body_MEM >> simp[check_function_body_in_mode_def] >>
     conj_tac >- (qexists_tac `F` >> simp[]) >>
     qexistsl_tac [`name`, `rr`] >>
     simp[check_function_body_in_mode_def]) >>
  qpat_assum `!mode a. _` (qspecl_then [`F`, `runtime_art`] mp_tac) >>
  simp[supported_declaration_body_def, supported_pure_exprs_every] >>
  Cases_on `vis` >> gvs[supported_deploy_declaration_def] >>
  fs[supported_default_expression_def, supported_expr_def, EVERY_MEM]
QED
