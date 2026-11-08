(* One selected package, with shared check, registration and body endpoints. *)
Theory selectedEntryPrefixCode
Ancestors selectedBodyCode runtimeExternalPackageCode entryCheckIntervals
  actualRegistrationCode loweringShapeProps loweringShapeDefs loweringShapeRules
  sourceEntryCode supportedProgram supportedProgramProps supportedDecls compileEnv moduleLowering
  fragExec compileVyper list packagedRegistrationProps argumentRegistrationOpen
  exprOpenPrimitives vyperLoweringCorrect vyperCompiler venomWf venomInst
  exprOpenTerminals allocaFrontierBound

Theorem source_selected_entry_prefix_code:
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
  ?fb ds de opened st cenv sa st'.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    compile_entry_checks min_cds is_payable opened = ((),st) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((),st') /\
    fn_has_code ds de efn /\ fn_has_code opened st efn /\
    fn_has_code st sa efn /\ fn_has_code sa st' efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    shape_state opened /\ shape_state st /\ shape_state sa /\
    de.cs_next_var <= opened.cs_next_var
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
  `MEM (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) extpkgs` by
    (qpat_x_assum `set_external_package_target _ _ = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `extpkgs = _` (fn th => rewrite_tac[th]) >>
     simp[MEM_MAP] >>
     qexists_tac `(mut,F,lookup_raw_return_or_F (NONE:num option) name External tops,
        name,args,([] : expr list),ret,fbody)` >> simp[]) >>
  qpat_x_assum `MEM (lbl,_,_,_,_,_,_,_,_,_,_) extpkgs` mp_tac >>
  rewrite_tac[MEM_SPLIT] >> strip_tac >>
  qpat_x_assum `extpkgs = _ ++ _` SUBST_ALL_TAC >>
  drule_all external_selected_check_interval >> strip_tac >>
  `external_fn_shape_ok
     (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt)` by
    fs[EVERY_APPEND] >>
  fs[external_fn_shape_ok_def] >>
  drule_all external_function_registration_boundary >> strip_tac >>
  drule register_positional_args_suffix_extends >> strip_tac >>
  `shape_extends F jump_label_ok dispatch_st before` by
    (qspec_then `l1` mp_tac compile_external_fn_bodies_shape >>
     simp[shape_step_def] >> disch_then drule >> simp[]) >>
  `dispatch_st.cs_next_var <= opened.cs_next_var` by
    (qpat_x_assum `new_block _ _ = _` mp_tac >>
     simp[new_block_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[shape_extends_def]) >>
  `shape_state after` by
    (drule_all compile_external_function_body_shape >>
     simp[shape_step_def] >> disch_then drule >> simp[]) >>
  `cs_extends after external_st` by
    (qspec_then `l2` mp_tac compile_external_fn_bodies_shape >>
     simp[shape_step_def] >> disch_then drule >> simp[shape_extends_def]) >>
  qexistsl_tac [`fallback`, `label_st`, `dispatch_st`, `opened`, `checked`,
    `ce`, `registered`, `after`] >>
  gvs[] >> rpt conj_tac
  >- (irule fn_has_code_mid >> metis_tac[])
  >- (irule fn_has_code_mid >> simp[] >>
      qexistsl_tac [`external_st`, `dispatch_st`] >> simp[] >>
      conj_tac >- (irule cs_extends_trans >> qexists_tac `after` >> simp[]) >>
      irule cs_extends_trans >> qexists_tac `opened` >> simp[])
  >- (irule fn_has_code_mid >> simp[] >>
      qexistsl_tac [`external_st`, `dispatch_st`] >> simp[] >>
      irule cs_extends_trans >> qexists_tac `opened` >> simp[] >>
      irule cs_extends_trans >> qexists_tac `checked` >> simp[]) >>
  qpat_x_assum `new_block _ _ = _` mp_tac >>
  simp[new_block_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[block_is_terminated_def]
QED

Theorem compile_entry_checks_open:
  !min_cds pay st u st'.
    ~block_is_terminated st /\ compile_entry_checks min_cds pay st = (u,st') ==>
    ~block_is_terminated st'
Proof
  rpt gen_tac >> Cases_on `pay` >> Cases_on `4 < min_cds` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[] >>
  imp_res_tac emit_void_terminated >> gvs[is_terminator_def]
QED

Theorem lowered_runtime_function_inst_ids_distinct:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  MEM fn unit.cu_context.ctx_functions ==> fn_inst_ids_distinct fn
Proof
  strip_tac >> drule lower_vyper_runtime_unit_run_lowering >> strip_tac >>
  drule run_lowering_context_ok >>
  disch_then (mp_tac o MATCH_MP lowering_context_ok_static_integrity) >>
  strip_tac >> drule_all ctx_inst_ids_distinct_fn >>
  simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_inst_ids]
QED

Theorem source_selected_entry_prefix_structure:
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
  ?fb ds de opened st cenv sa st'.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    compile_entry_checks min_cds is_payable opened = ((),st) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((),st') /\
    fn_has_code ds de efn /\ fn_has_code opened st efn /\
    fn_has_code st sa efn /\ fn_has_code sa st' efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    shape_state opened /\ shape_state st /\ shape_state sa /\
    de.cs_next_var <= opened.cs_next_var /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    cenv.ce_return_buf = NONE /\ fn_inst_ids_distinct efn
Proof
  strip_tac >> drule_all source_selected_entry_prefix_code >> strip_tac >>
  drule_all target_external_registration_locals >> strip_tac >>
  drule_all compile_entry_checks_open >> strip_tac >>
  drule_all compile_register_positional_args_open >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  drule_all lowered_runtime_function_inst_ids_distinct >> strip_tac >>
  qexistsl_tac [`fb`, `ds`, `de`, `opened`, `st`, `cenv`, `sa`, `st'`] >> simp[]
QED
