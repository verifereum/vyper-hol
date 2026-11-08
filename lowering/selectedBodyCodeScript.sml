(* Compilation intervals for a selected packaged external body. *)
Theory selectedBodyCode
Ancestors actualRegistrationCode moduleLowering compileEnv
  loweringShapeDefs loweringShapeRules loweringShapeProps fragExec list
  sourceEntryCode compileVyper vyperInterpreter supportedProgramProps
  entryDispatchProps rawEntryCode entryCheckIntervals sourceEntrySelection
  supportedProgram supportedDecls loweringShapeSource compileEnv supportedNames
  vyperCompiler actualDecoderPackaging

Theorem external_selected_body_boundary:
  compile_external_fn_bodies
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix)
    st = ((),stf) /\ shape_state st /\
  EVERY external_fn_shape_ok
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix) ==>
  ?first ce registered body_end.
    compile_register_positional_args cenv args 4 first = (ce,registered) /\
    compile_guarded_body ce nr nkey transient view ss ret_type registered = ((),body_end) /\
    shape_state registered /\ cs_extends st first /\
    cs_extends registered body_end /\ cs_extends body_end stf
Proof
  strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  rewrite_tac[external_bodies_append] >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies (_::_) _ = _` mp_tac >>
  pure_once_rewrite_tac[external_bodies_cons_split] >> strip_tac >>
  fs[EVERY_APPEND] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_singleton_body_boundary >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies prefix _ = _` kall_tac >>
  `EVERY external_fn_shape_ok
    [(lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)]` by simp[] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies [_] _ = _` kall_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  fs[external_fn_shape_ok_def] >>
  drule_all external_function_registration_boundary >> strip_tac >>
  goal_assum $ drule_at Any >> metis_tac[cs_extends_trans]
QED

Theorem external_lookup_raw_package_member:
  !tops src name mut nr args dflts ret body.
    vyperInterpreter$lookup_function src name External tops =
      SOME (mut,nr,args,dflts,ret,body) /\ name <> "__default__" /\
    (!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops) /\
    (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops) ==>
    MEM (mut,nr,lookup_raw_return_or_F src name External tops,
         name,args,dflts,ret,body) (FST (classify_functions tops))
Proof
  Induct >- simp[vyperInterpreterTheory.lookup_function_def] >>
  rpt gen_tac >> strip_tac >> fs[classify_functions_def] >>
  `?a1 a2 a3 a4. FOLDR classify_function ([],[],NONE,NONE) tops =
                 (a1,a2,a3,a4)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  fs[] >> Cases_on `h` >>
  TRY (qmatch_goalsub_rename_tac `FunctionDecl vis _ _ _ _ _ _ _ _` >>
       Cases_on `vis`) >>
  TRY (qmatch_goalsub_rename_tac `VariableDecl vis _ _ _ _` >>
       Cases_on `vis`) >>
  TRY (qmatch_goalsub_rename_tac `HashMapDecl vis _ _ _ _ _` >>
       Cases_on `vis`) >>
  gvs[vyperInterpreterTheory.lookup_function_def, classify_function_def,
      lookup_raw_return_or_F_def, lookup_raw_return_def] >>
  rw[] >> gvs[] >>
  TRY (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> rw[]) >>
  metis_tac[]
QED

Theorem source_selected_body_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) name External tops,
       name,args,([] : expr list),ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) ==>
  ?st cenv sa st'.
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((),st') /\
    fn_has_code sa st' efn /\ shape_state sa /\ cs_extends sa st'
Proof
  strip_tac >>
  `!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  `!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  drule_all external_lookup_raw_package_member >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  simp[] >> strip_tac >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
    (build_selectors (type_env tops) exts)` by
    rewrite_tac[build_selectors_fn_labels] >>
  `EVERY external_fn_shape_ok
    (MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> gs[]) >>
  `EVERY internal_fn_shape_ok
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) F 0) ints)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok (set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot) fb))` by
    (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
       `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >> gs[]) >>
  gvs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
    internal_fn_descriptors_MAP_package_internal_fn] >>
  qmatch_asmsub_abbrev_tac `run_lowering sels extpkgs intpkgs fbpkg` >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  Cases_on `compile_generate_runtime sels extpkgs intpkgs fbpkg Linear 0 0 []
    (build_dense_entry_info sels extpkgs) (initial_compile_state "__entry")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule runtime_external_boundary >>
  impl_tac >- simp[shape_state_initial_compile_state] >> strip_tac >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors intpkgs) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors intpkgs))` by
    simp[Abbr `intpkgs`, internal_fn_descriptors_set_internal_package_target,
      internal_fn_descriptors_MAP_package_internal_fn] >>
  `MEM (mk_raw_function "__entry" (all_blocks entry_end))
    unit.cu_context.ctx_functions` by
    (drule run_lowering_packaged_entry_member >>
     disch_then (qspecl_then [`r`, `final`, `entry_end`] mp_tac) >> simp[]) >>
  `shape_state (initial_compile_state "__entry")` by
    simp[shape_state_initial_compile_state] >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    simp[Abbr `sels`, build_selectors_fn_labels] >>
  drule_all runtime_dispatch_shape_boundary >> strip_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_fallback_suffix_extends >> strip_tac >>
  drule_all run_lowering_entry_interval >> strip_tac >>
  `MEM (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt)
    extpkgs` by
    (qpat_x_assum `set_external_package_target _ _ = _` (SUBST1_TAC o SYM) >>
     simp_tac pure_ss [Abbr `extpkgs`, MEM_MAP] >>
     qexists_tac `package_external_fn tops T (K global_nonreentrant_slot)
       (mut,F,lookup_raw_return_or_F (NONE:num option) name External tops,
        name,args,([] : expr list),ret,fbody)` >>
     conj_tac >- REFL_TAC >>
     qexists_tac `(mut,F,lookup_raw_return_or_F (NONE:num option) name External tops,
        name,args,([] : expr list),ret,fbody)` >>
     conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `MEM (lbl,_,_,_,_,_,_,_,_,_,_) extpkgs` mp_tac >>
  rewrite_tac[MEM_SPLIT] >> strip_tac >>
  qpat_x_assum `extpkgs = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [APPEND]) >>
  drule_all external_selected_body_boundary >> strip_tac >>
  `cs_extends body_end entry_end` by metis_tac[cs_extends_trans] >>
  `fn_has_code registered body_end efn` by
    (gvs[] >> irule external_decoder_fn_has_code >>
     simp[] >> qexists_tac `registered` >> simp[cs_extends_refl]) >>
  qexistsl_tac [`first`, `ce`, `registered`, `body_end`] >> simp[]
QED
