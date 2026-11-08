(* Source classification probes for entry ownership. *)
Theory sourceEntryCode
Ancestors runtimeExternalPackageCode supportedProgramProps entryDispatchProps compileVyper
  rawEntryCode entryCheckIntervals sourceEntrySelection supportedProgram supportedDecls
  loweringShapeSource loweringShapeProps loweringShapeDefs compileEnv supportedNames list
  vyperCompiler actualDecoderPackaging actualRegistrationCode moduleLowering

Theorem supported_fallback_not_external_table:
  supported_program
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]] /\
  vyperInterpreter$lookup_function NONE "__default__" External
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]] =
    SOME (Payable,F,[],[],NoneT,[Pass]) /\
  FST (classify_functions
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]]) = []
Proof
  EVAL_TAC
QED

Theorem supported_external_lookup_member:
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?rr. MEM (mut,nr,rr,name,args,dflts,ret,fbody)
    (FST (classify_functions tops))
Proof
  strip_tac >>
  `!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  `!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  drule_all lookup_function_external_mem >> simp[]
QED

Theorem source_runtime_entry_witness:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?sels extpkgs fallback label_st dispatch_st external_st entry_end
    cenv pos_args min_cds nkey transient view ret_type.
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    MEM ("fn_" ++ name,cenv,pos_args,min_cds,mut = Payable,F,nkey,
      transient,view,fbody,ret_type) extpkgs /\
    EVERY external_fn_shape_ok extpkgs /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fallback label_st = ((),dispatch_st) /\
    compile_external_fn_bodies extpkgs dispatch_st = ((),external_st) /\
    shape_state dispatch_st /\
    cs_extends label_st dispatch_st /\
    cs_extends dispatch_st external_st /\ cs_extends external_st entry_end /\
    efn = mk_raw_function "__entry" (all_blocks entry_end) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) /\
    fn_has_code label_st dispatch_st efn /\ fn_has_code dispatch_st external_st efn
Proof
  strip_tac >> drule_all supported_external_lookup_member >> strip_tac >>
  drule_all source_runtime_external_packages >> strip_tac >>
  qexistsl_tac [`build_selectors (type_env tops) (FST (classify_functions tops))`,
    `extpkgs`, `fallback`, `label_st`, `dispatch_st`, `external_st`, `entry_end`] >>
  simp[] >>
  `MEM (set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,rr,name,args,([] : expr list),ret,fbody))) extpkgs` by
    (simp_tac pure_ss [Once EQ_SYM_EQ] >>
     qpat_x_assum `extpkgs = _` (fn th => rewrite_tac[th]) >>
     simp[MEM_MAP] >>
     qexists_tac `(mut,F,rr,name,args,([] : expr list),ret,fbody)` >> simp[]) >>
  pop_assum mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  metis_tac[]
QED

Theorem source_selected_entry_check_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?fb ds de opened checked min_cds.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    fn_has_code ds de efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\
    ds.cs_next_var = 0 /\
    compile_entry_checks min_cds (mut = Payable) opened = ((),checked) /\
    fn_has_code opened checked efn /\
    opened.cs_current_bb = "fn_" ++ name /\
    opened.cs_current_insts = [] /\ ~block_is_terminated opened
Proof
  strip_tac >> drule_all source_runtime_entry_witness >> strip_tac >>
  drule_all installed_selected_check_code >> strip_tac >>
  `label_st.cs_blocks = [] /\ label_st.cs_current_insts = [] /\
   label_st.cs_next_var = 0 /\
   label_st.cs_current_bb = (initial_compile_state "__entry").cs_current_bb` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, initial_compile_state_def] >>
     strip_tac >> gvs[]) >>
  `cs_extends label_st entry_end` by metis_tac[cs_extends_trans] >>
  drule_all cs_extends_raw_entry_label >>
  disch_then (qspec_then `"__entry"` mp_tac) >>
  gvs[] >> strip_tac >>
  qexistsl_tac [`fallback`, `label_st`, `dispatch_st`, `opened`, `checked`, `min_cds`] >>
  simp[]
QED
