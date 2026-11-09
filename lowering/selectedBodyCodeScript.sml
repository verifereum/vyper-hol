(* Compilation intervals for a selected packaged external body. *)
Theory selectedBodyCode
Ancestors actualRegistrationCode moduleLowering compileEnv
  loweringShapeDefs loweringShapeRules loweringShapeProps fragExec list
  sourceEntryCode runtimeExternalPackageCode compileVyper vyperInterpreter supportedProgramProps
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
    (package_external_fn tops F (assign_nkeys tops 0)
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
  drule_all source_runtime_external_packages >> strip_tac >>
  `MEM (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt)
    extpkgs` by
    (qpat_x_assum `set_external_package_target _ _ = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `extpkgs = _` (fn th => rewrite_tac[th]) >>
     simp[MEM_MAP] >>
     qexists_tac `(mut,F,lookup_raw_return_or_F (NONE:num option) name External tops,
        name,args,([] : expr list),ret,fbody)` >> simp[]) >>
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
