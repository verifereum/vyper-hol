(* Compilation intervals for a selected packaged external body. *)
Theory selectedBodyCode
Ancestors actualRegistrationCode moduleLowering compileEnv
  loweringShapeDefs loweringShapeRules loweringShapeProps fragExec list
  sourceEntryCode compileVyper vyperInterpreter supportedProgramProps
  entryDispatchProps constSubst rawEntryCode entryCheckIntervals sourceEntrySelection
  runtimeExternalPackageCode
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

Theorem source_selected_body_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel NONE) tops)) /\
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
    compile_guarded_body cenv F nkey ut' iv
      (subst_consts_stmts (module_consts_env tops []) fbody) rt sa = ((),st') /\
    fn_has_code sa st' efn /\ shape_state sa /\ cs_extends sa st'
Proof
  strip_tac >>
  drule_all lookup_function_external_raw_member >> strip_tac >>
  drule_all source_runtime_external_packages >> strip_tac >>
  `set_external_package_target rpolicy.rpol_target
     (package_external_fn tops T (K global_nonreentrant_slot)
       (subst_consts_fn (module_consts_env tops [])
         (mut,F,lookup_raw_return_or_F (NONE:num option) name External tops,
          name,args,[],ret,fbody))) =
   (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,
    subst_consts_stmts (module_consts_env tops []) fbody,rt)` by
    (rewrite_tac[GSYM external_package_subst_consts] >> simp[]) >>
  `MEM (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,
      subst_consts_stmts (module_consts_env tops []) fbody,rt) extpkgs` by
    (pop_assum (SUBST1_TAC o SYM) >>
     qpat_x_assum `extpkgs = _` SUBST1_TAC >>
     simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
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
