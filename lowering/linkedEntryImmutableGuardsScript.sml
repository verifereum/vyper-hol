(* Discharge allocation guards for the selected, rewritten function body. *)
Theory linkedEntryImmutableGuards
Ancestors
  linkedOwnedImmutableLocation linkedConstAccessSubset bodyInvSplit
  exprSimHypsDefs supportedStmtTraverse supportedExprTraverse
  vyperTypeContractStaticMaps vyperTypeContract vyperSubscriptOverlap
  vyperInterpreter constSubstMods constSubst compileEnv vyperAST alist finite_map list pair

val _ = Parse.hide "body";

Triviality expression_root_access_cover:
  (!e. p e ==> ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_expr e)) ==>
  (!e. supported_expr_exists p e ==>
       ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_expr e)) /\
  (!t. supported_target_exists p t ==>
       ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_target t)) /\
  (!es. supported_exprs_exists p es ==>
        ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_exprs es)) /\
  (!opt. supported_opt_exists p opt ==>
         ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_opt opt)) /\
  (!fields. supported_fields_exists p fields ==>
            ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_named_exprs fields))
Proof
  strip_tac >> ho_match_mp_tac accesses_expr_ind >>
  simp[supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
  rpt strip_tac >>
  res_tac >> fs[accesses_expr_def, MEM_APPEND] >> metis_tac[]
QED

Triviality substituted_roots_keep_access:
  (!e. p e ==> ?ty key. e = TopLevelName ty key /\ P key) /\
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) ==>
  (!e. supported_expr_exists p (subst_consts_expr_mods E e) ==>
       ?key. P key /\ ALOOKUP E key = NONE /\
         MEM (ReadAcc (StateRef key)) (accesses_expr (subst_consts_expr_mods E e))) /\
  (!t. supported_target_exists p (subst_consts_btarget_mods E t) ==>
       ?key. P key /\ ALOOKUP E key = NONE /\
         MEM (ReadAcc (StateRef key)) (accesses_target (subst_consts_btarget_mods E t))) /\
  (!es. supported_exprs_exists p (subst_consts_exprs_mods E es) ==>
        ?key. P key /\ ALOOKUP E key = NONE /\
          MEM (ReadAcc (StateRef key)) (accesses_exprs (subst_consts_exprs_mods E es))) /\
  (!opt. supported_opt_exists p (subst_consts_opt_mods E opt) ==>
         ?key. P key /\ ALOOKUP E key = NONE /\
           MEM (ReadAcc (StateRef key)) (accesses_opt (subst_consts_opt_mods E opt))) /\
  (!fields. supported_fields_exists p (subst_consts_fields_mods E fields) ==>
            ?key. P key /\ ALOOKUP E key = NONE /\
              MEM (ReadAcc (StateRef key)) (accesses_named_exprs (subst_consts_fields_mods E fields)))
Proof
  strip_tac >>
  `!e. accesses_expr e = [] ==> ~supported_expr_exists p e` by
    (`!e. p e ==> ?key. P key /\ MEM (ReadAcc (StateRef key)) (accesses_expr e)` by
       (rpt strip_tac >> res_tac >> gvs[accesses_expr_def]) >>
     drule_then (assume_tac o cj 1) expression_root_access_cover >>
     metis_tac[MEM]) >>
  ho_match_mp_tac accesses_expr_ind >>
  simp[subst_consts_expr_mods_def, supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
  rpt strip_tac >>
  res_tac >> gvs[]
  >~ [`subst_consts_expr_mods E (TopLevelName _ _)`]
  >- (rename1 `subst_consts_expr_mods E (TopLevelName ty nsid)` >>
      PairCases_on `nsid` >> Cases_on `ALOOKUP E (nsid0,nsid1)` >>
      gvs[subst_consts_expr_mods_def, accesses_expr_def, supported_expr_exists_def] >>
      res_tac >> gvs[]) >>
  metis_tac[]
QED

Triviality substituted_stmt_roots_keep_access:
  (!e. p e ==> ?ty key. e = TopLevelName ty key /\ P key) /\
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) ==>
  !ss. supported_stmts_expr_exists p (subst_consts_stmts_mods E ss) ==>
       ?key. P key /\ ALOOKUP E key = NONE /\
         MEM (ReadAcc (StateRef key)) (accesses_stmts (subst_consts_stmts_mods E ss))
Proof
  strip_tac >>
  drule_all_then (map_every assume_tac o CONJUNCTS) substituted_roots_keep_access >>
  `(!t. supported_assignment_exists p (subst_consts_target_mods E t) ==>
        ?key. P key /\ ALOOKUP E key = NONE /\
          MEM (ReadAcc (StateRef key)) (accesses_atarget (subst_consts_target_mods E t))) /\
    (!ts. supported_assignments_exists p (subst_consts_targets_mods E ts) ==>
          ?key. P key /\ ALOOKUP E key = NONE /\
            MEM (ReadAcc (StateRef key)) (accesses_atargets (subst_consts_targets_mods E ts)))` by
    (ho_match_mp_tac accesses_atarget_ind >>
     simp[subst_consts_target_mods_def, supported_assignment_exists_def, accesses_atarget_def, MEM_APPEND] >>
     metis_tac[]) >>
  `!es. supported_exprs_exists p es <=> EXISTS (supported_expr_exists p) es` by
    (Induct >> simp[supported_expr_exists_def]) >>
  `!es fs. accesses_exprs (es ++ fs) = accesses_exprs es ++ accesses_exprs fs` by
    (Induct >> simp[accesses_expr_def]) >>
  `!fields. accesses_exprs (MAP SND fields) = accesses_named_exprs fields /\
            EXISTS (supported_expr_exists p) (MAP SND fields) = supported_fields_exists p fields` by
    (Induct >> simp[accesses_expr_def, supported_expr_exists_def, FORALL_PROD]) >>
  `!err. EXISTS (supported_expr_exists p) (custom_error_exprs (subst_consts_error_mods E err)) ==>
    ?key. P key /\ ALOOKUP E key = NONE /\
      MEM (ReadAcc (StateRef key))
          (accesses_exprs (custom_error_exprs (subst_consts_error_mods E err)))` by
    (Cases >> simp[custom_error_exprs_def, subst_consts_error_mods_def, MEM_APPEND, EXISTS_APPEND] >>
     metis_tac[]) >>
  `(!s. supported_stmt_expr_exists p (subst_consts_stmt_mods E s) ==>
        ?key. P key /\ ALOOKUP E key = NONE /\
          MEM (ReadAcc (StateRef key)) (accesses_stmt (subst_consts_stmt_mods E s))) /\
    (!ss. supported_stmts_expr_exists p (subst_consts_stmts_mods E ss) ==>
          ?key. P key /\ ALOOKUP E key = NONE /\
            MEM (ReadAcc (StateRef key)) (accesses_stmts (subst_consts_stmts_mods E ss)))`
    suffices_by (strip_tac >> first_assum ACCEPT_TAC) >>
  ho_match_mp_tac accesses_stmt_ind >>
  simp[subst_consts_stmt_mods_def, supported_stmt_expr_exists_def, accesses_stmt_def, MEM_APPEND] >>
  rpt strip_tac >> res_tac >> fs[]
  >~ [`supported_iterator_exists _ (subst_consts_iter_mods _ _)`]
  >- (rename1 `supported_iterator_exists p (subst_consts_iter_mods E iter)` >>
      Cases_on `iter` >>
      fs[subst_consts_iter_mods_def, supported_iterator_exists_def, accesses_iterator_def, MEM_APPEND] >>
      metis_tac[])
  >~ [`supported_assert_exists _ (subst_consts_areason_mods _ _)`]
  >- (rename1 `supported_assert_exists p (subst_consts_areason_mods E reason)` >>
      Cases_on `reason` >>
      fs[subst_consts_areason_mods_def, supported_assert_exists_def, accesses_assert_reason_def] >>
      metis_tac[]) >>
  all_tac
  >~ [`supported_raise_exists _ (subst_consts_rreason_mods _ _)`]
  >- (rename1 `supported_raise_exists p (subst_consts_rreason_mods E reason)` >>
      Cases_on `reason` >>
      fs[subst_consts_rreason_mods_def, supported_raise_exists_def, accesses_raise_reason_def] >>
      metis_tac[]) >>
  metis_tac[]
QED

Triviality module_const_key_mem:
  !src tops E key.
    MEM key (MAP FST E) \/
    (?vis e id ty slot. key = (src,id) /\ MEM (VariableDecl vis (Constant e) id ty slot) tops) ==>
    MEM key (MAP FST (module_consts_env_mods src tops E))
Proof
  ho_match_mp_tac module_consts_env_mods_ind >>
  simp[module_consts_env_mods_def, MEM_APPEND] >> metis_tac[]
QED

Triviality ordered_const_key_mem:
  !mods E key.
    MEM key (MAP FST E) \/
    (?src tops vis e id ty slot. key = (src,id) /\ MEM (src,tops) mods /\
      MEM (VariableDecl vis (Constant e) id ty slot) tops) ==>
    MEM key (MAP FST (consts_env_mods_acc mods E))
Proof
  Induct >> simp[consts_env_mods_acc_def, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[module_const_key_mem]
QED

Theorem substituted_stmts_const_name_free_mods:
  (!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==> accesses_expr rhs = []) ==>
  ~supported_stmts_expr_exists (const_name_root_mods mods)
    (subst_consts_stmts_mods (consts_env_mods mods) ss)
Proof
  strip_tac >>
  `!tops E id. MEM id (MAP FST (module_consts_env tops E)) ==>
    MEM id (MAP FST E) \/
    ?vis e ty slot. MEM (VariableDecl vis (Constant e) id ty slot) tops` by
    (ho_match_mp_tac constSubstTheory.module_consts_env_ind >>
     simp[constSubstTheory.module_consts_env_def, MEM_APPEND] >> metis_tac[]) >>
  `!key. cx_const_name_mods mods key ==>
    ALOOKUP (consts_env_mods mods) key <> NONE` by
    (gen_tac >> PairCases_on `key` >>
     simp[NoAsms, cx_const_name_mods_def, ALOOKUP_NONE, consts_env_mods_def,
          consts_env_modules_order_eq] >>
     disch_then (qx_choose_then `decls` strip_assume_tac) >>
     `MEM (key0,decls) mods` by (irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
     qpat_assum `!tops E id. MEM id (MAP FST (module_consts_env tops E)) ==> _`
       (qspecl_then [`decls`,`[]`,`key1`] (fn origin =>
          qpat_assum `MEM key1 (MAP FST (module_consts_env decls []))`
            (strip_assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP origin))) >>
     irule ordered_const_key_mem >> simp[MEM_constants_order] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`p` |-> `const_name_root_mods mods`,
                  `P` |-> `cx_const_name_mods mods`,
                  `E` |-> `consts_env_mods mods`] substituted_stmt_roots_keep_access) >>
  impl_tac
  >- (conj_tac >- (Cases >> simp[const_name_root_mods_def]) >>
      first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `ss` (fn roots =>
    strip_tac >>
    qpat_assum `supported_stmts_expr_exists (const_name_root_mods mods) _`
      (qx_choose_then `key` strip_assume_tac o MATCH_MP roots))) >>
  qpat_assum `!key. cx_const_name_mods mods key ==> _`
    (drule_then (fn present => qpat_assum `ALOOKUP (consts_env_mods mods) key = NONE`
      (ACCEPT_TAC o REWRITE_RULE [present])))
QED

Theorem linked_checked_body_immutable_guards:
  check_contract mode layouts addr mods = SOME art /\
  check_linked_state_ownership layouts addr mods (linked_live_functions mods exps) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret body) tops /\
  MEM (src,name) (linked_live_functions mods exps) /\
  env.bare_globals = art.cta_bare_globals /\
  env.bare_global_assignable = art.cta_bare_global_assignable /\
  immutable_section_layout_mods mods ce /\
  (!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> accesses_expr r = []) ==>
  ~supported_stmts_expr_exists (unallocated_bare_global_root ce env)
    (subst_consts_stmts_mods (consts_env_mods mods) body) /\
  (!key. MEM (WriteAcc (StateRef key))
          (accesses_stmts (subst_consts_stmts_mods (consts_env_mods mods) body)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP ce.ce_module_vars key))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac check_contract_runtime_namespaces >>
  drule_then (map_every assume_tac o CONJUNCTS) check_contract_nonsig_maps >>
  `!key. (MEM (ReadAcc (StateRef key))
              (accesses_stmts (subst_consts_stmts_mods (consts_env_mods mods) body)) \/
           MEM (WriteAcc (StateRef key))
              (accesses_stmts (subst_consts_stmts_mods (consts_env_mods mods) body))) ==>
          (mods = [(NONE,tops)] \/ linked_state_ref_allocated layouts addr mods key)` by
    (gen_tac >> disch_tac >>
     drule_then (assume_tac o cj 2) linked_subst_accesses_subset >>
     Q.SUBGOAL_THEN
       `MEM (ReadAcc (StateRef key)) (accesses_stmts body) \/
        MEM (WriteAcc (StateRef key)) (accesses_stmts body)` assume_tac
     >- metis_tac[] >>
     `((case mods of [(NONE,_)] => T | _ => F) <=>
       ?mtops. mods = [(NONE,mtops)])` by
       (Cases_on `mods` >> simp[] >> PairCases_on `h` >>
        Cases_on `h0` >> Cases_on `t` >> simp[]) >>
     `MEM (src,tops) mods` by (irule ALOOKUP_MEM >> simp[]) >>
     qpat_x_assum `check_linked_state_ownership _ _ _ _` mp_tac >>
     simp[check_linked_state_ownership_def] >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac mp_tac)
     >- fs[] >>
     simp[Once EVERY_MEM] >>
     qpat_assum `MEM (src,tops) mods` (fn member =>
       disch_then (mp_tac o (C MATCH_MP member))) >>
     simp[Once EVERY_MEM] >>
     qpat_assum `MEM (FunctionDecl vis mut nr raw name args dflts ret body) tops`
       (fn decl => disch_then (mp_tac o (C MATCH_MP decl))) >>
     asm_simp_tac (srw_ss()) [EVERY_MEM, MEM_APPEND] >>
     strip_tac >> disj2_tac >>
     qpat_assum `!a. MEM a (accesses_stmts body) ==> _` (fn owned =>
       qpat_x_assum `MEM (ReadAcc (StateRef key)) (accesses_stmts body) \/ _`
         (DISJ_CASES_THEN (mp_tac o MATCH_MP owned))) >> simp[]) >>
  `!isrc itops ivis id ty slot.
     ALOOKUP mods isrc = SOME itops /\
     MEM (VariableDecl ivis Immutable id ty slot) itops /\
     (mods = [(NONE,tops)] \/ linked_state_ref_allocated layouts addr mods (isrc,id)) ==>
     IS_SOME (FLOOKUP ce.ce_module_vars (isrc,id))` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     Q.SUBGOAL_THEN
       `mods = [(NONE,itops)] \/ linked_state_ref_allocated layouts addr mods (isrc,id)`
       assume_tac
     >- (qpat_x_assum `mods = [(NONE,tops)] \/ _` (DISJ_CASES_THEN assume_tac) >> fs[]) >>
     drule_all_then strip_assume_tac linked_owned_immutable_location >> simp[]) >>
  conj_tac
  >- (strip_tac >>
      mp_tac (Q.INST [`p` |-> `unallocated_bare_global_root ce env`,
                      `P` |-> `\key. IS_SOME (FLOOKUP env.bare_globals key) /\
                                      FLOOKUP ce.ce_module_vars key = NONE`,
                      `E` |-> `consts_env_mods mods`] substituted_stmt_roots_keep_access) >>
      BETA_TAC >>
      impl_tac >- (asm_rewrite_tac[] >> Cases >> simp[unallocated_bare_global_root_def] >> metis_tac[]) >>
      disch_then (qspec_then `body : stmt list` mp_tac) >>
      asm_rewrite_tac[] >> disch_then (qx_choose_then `key` strip_assume_tac) >>
      PairCases_on `key` >>
      `?ty. FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (key0,key1) = SOME ty` by
        fs[optionTheory.IS_SOME_EXISTS] >>
      drule_all_then strip_assume_tac build_contract_type_artifact_bare_globals_sound
      >- (gvs[] >>
          qpat_assum `!isrc itops ivis id ty slot. _ ==> IS_SOME _`
            (qspecl_then [`key0`,`ts`,`vis'`,`id_str`,`ty`,`init`] mp_tac) >>
          qpat_assum `!key. _ ==> mods = [(NONE,tops)] \/ _`
            (qspec_then `(key0,id_str)` mp_tac) >> simp[]) >>
      `MEM (key0,key1) (MAP FST (consts_env_mods mods))` by
        (simp[consts_env_mods_def, consts_env_modules_order_eq] >> irule ordered_const_key_mem >>
         simp[MEM_constants_order] >> metis_tac[ALOOKUP_MEM]) >>
      gvs[ALOOKUP_NONE]) >>
  Cases_on `mode`
  >~ [`check_contract F layouts addr mods = SOME art`]
  >- (drule_then strip_assume_tac check_contract_runtime_assignable >> simp[]) >>
  rpt strip_tac >> PairCases_on `key` >>
  qpat_x_assum `IS_SOME (FLOOKUP env.bare_global_assignable _)`
    (qx_choose_then `ity` mp_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_assum `env.bare_global_assignable = art.cta_bare_global_assignable`
    (PURE_REWRITE_TAC o single) >>
  qpat_assum `art.cta_bare_global_assignable = _` (PURE_REWRITE_TAC o single) >>
  strip_tac >>
  drule_then assume_tac (cj 1 check_contract_artifact_fields) >>
  drule_all_then
    (qx_choosel_then [`itops`,`ivis`,`id_str`,`init`] (map_every assume_tac o CONJUNCTS))
    build_contract_type_artifact_bare_global_assignable_sound >>
  qpat_x_assum `key1 = id_str` SUBST_ALL_TAC >>
  qpat_assum `!isrc itops ivis id ty slot. _ ==> IS_SOME _`
    (qspecl_then [`key0`,`itops`,`ivis`,`id_str`,`ity`,`init`] mp_tac) >>
  qpat_assum `!key. _ ==> mods = [(NONE,tops)] \/ _`
    (qspec_then `(key0,id_str)` mp_tac) >> simp[]
QED

Theorem linked_checked_default_immutable_guards:
  check_contract F layouts addr mods = SOME art /\
  check_linked_state_ownership layouts addr mods (linked_live_functions mods exps) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl External mut nr raw name args dflts ret body) tops /\
  MEM (src,name) (linked_live_functions mods exps) /\
  env.bare_globals = art.cta_bare_globals /\
  immutable_section_layout_mods mods ce /\
  (!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> accesses_expr r = []) ==>
  ~supported_exprs_exists (unallocated_bare_global_root ce env)
    (subst_consts_exprs_mods (consts_env_mods mods) dflts)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac check_contract_runtime_namespaces >>
  drule_then (map_every assume_tac o CONJUNCTS) check_contract_nonsig_maps >>
  `!key. MEM (ReadAcc (StateRef key)) (accesses_exprs dflts) ==>
         ((?mtops. mods = [(NONE,mtops)]) \/
           linked_state_ref_allocated layouts addr mods key)` by
    (gen_tac >> strip_tac >>
     qpat_assum `check_linked_state_ownership _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC [check_linked_state_ownership_def] >>
     disch_then (DISJ_CASES_THEN2 mp_tac assume_tac)
     >- (Cases_on `mods` >> simp[NoAsms] >> PairCases_on `h` >>
         Cases_on `h0` >> Cases_on `t` >> simp[NoAsms]) >>
     `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
     qpat_assum `EVERY _ mods` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(src,tops)` mp_tac) >>
     qpat_assum `MEM (src,tops) mods` (fn member => simp[NoAsms, member]) >>
     PURE_REWRITE_TAC [Once EVERY_MEM] >>
     qpat_assum `MEM (FunctionDecl External mut nr raw name args dflts ret body) tops`
       (fn decl => disch_then (mp_tac o C MATCH_MP decl)) >>
     qpat_assum `MEM (src,name) (linked_live_functions mods exps)`
       (fn live => simp[NoAsms, live, EVERY_MEM, MEM_APPEND]) >>
     strip_tac >> disj2_tac >>
     qpat_assum `!a. MEM a (accesses_exprs dflts) \/ _ ==> _`
       (qspec_then `ReadAcc (StateRef key)` mp_tac) >>
     qpat_assum `MEM (ReadAcc (StateRef key)) (accesses_exprs dflts)`
       (fn read => simp[NoAsms, read])) >>
  strip_tac >>
  mp_tac (Q.INST [`p` |-> `unallocated_bare_global_root ce env`,
     `P` |-> `\key. IS_SOME (FLOOKUP env.bare_globals key) /\
                    FLOOKUP ce.ce_module_vars key = NONE`,
     `E` |-> `consts_env_mods mods`] substituted_roots_keep_access) >>
  BETA_TAC >>
  impl_tac >- (asm_rewrite_tac[] >> Cases >>
               simp[unallocated_bare_global_root_def] >> metis_tac[]) >>
  disch_then (qspecl_then [`dflts:expr list`] mp_tac o cj 3) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choose_then `key` (map_every assume_tac o CONJUNCTS)) >>
  drule_then (assume_tac o cj 1) linked_subst_accesses_subset >>
  `MEM (ReadAcc (StateRef key)) (accesses_exprs dflts)` by
    (qpat_assum `!es a. MEM a (accesses_exprs (subst_consts_exprs_mods _ es)) ==> _`
       (drule_then ACCEPT_TAC)) >>
  PairCases_on `key` >>
  `?ty. FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (key0,key1) = SOME ty` by
    fs[optionTheory.IS_SOME_EXISTS] >>
  drule_all_then strip_assume_tac build_contract_type_artifact_bare_globals_sound
  >- (qpat_x_assum `key1 = id_str` SUBST_ALL_TAC >>
      `mods = [(NONE,ts)] \/ linked_state_ref_allocated layouts addr mods (key0,id_str)`
      suffices_by
        (disch_then (fn allocated =>
           qpat_assum `contract_namespaces_ok F mods` (fn namespaces =>
             qpat_assum `ALOOKUP mods key0 = SOME ts` (fn module =>
               qpat_assum `MEM (VariableDecl vis Immutable id_str ty init) ts` (fn decl =>
                 qpat_assum `immutable_section_layout_mods mods ce` (fn section =>
                   mp_tac (MATCH_MP linked_owned_immutable_location
                     (LIST_CONJ [namespaces,module,decl,allocated,section]))))))) >>
         qpat_assum `FLOOKUP ce.ce_module_vars (key0,id_str) = NONE`
           (fn absent => simp[NoAsms, absent])) >>
      qpat_assum `!key. MEM (ReadAcc (StateRef key)) (accesses_exprs dflts) ==> _`
        (drule_then (DISJ_CASES_THEN2 (qx_choose_then `main_tops` assume_tac) assume_tac))
      >- (disj1_tac >>
          qpat_assum `mods = [(NONE,main_tops)]` (fn singleton =>
            qpat_assum `ALOOKUP mods key0 = SOME ts` mp_tac >>
            simp[NoAsms, singleton, AllCaseEqs()])) >>
      disj2_tac >> first_assum ACCEPT_TAC) >>
  `MEM (key0,key1) (MAP FST (consts_env_mods mods))` by
    (simp[consts_env_mods_def, consts_env_modules_order_eq] >>
     irule ordered_const_key_mem >> simp[MEM_constants_order] >> metis_tac[ALOOKUP_MEM]) >>
  gvs[ALOOKUP_NONE]
QED
