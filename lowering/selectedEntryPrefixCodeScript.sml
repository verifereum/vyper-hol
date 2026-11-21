(* One selected package, with shared check, registration and body endpoints. *)
Theory selectedEntryPrefixCode
Ancestors entryRejectCode entryCheckIntervals
  actualRegistrationCode loweringShapeProps loweringShapeDefs loweringShapeRules
  supportedProgram supportedProgramProps supportedDecls compileEnv moduleLowering
  fragExec compileVyper list packagedRegistrationProps argumentRegistrationOpen
  exprOpenPrimitives vyperLoweringCorrect vyperCompiler venomWf venomInst
  exprOpenTerminals allocaFrontierBound externalEntryChecks runtimeBodyStartDefs
  entryDispatchProps

Theorem classified_entry_prefix_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel NONE) tops)) /\
  MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,
     name,args,([] : expr list),ret,fbody)) (FST (classify_functions tops)) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (subst_consts_fn (module_consts_env tops [])
        (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,
         name,args,([] : expr list),ret,fbody))) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) ==>
  ?fb ds de opened st cenv sa st'.
    runtime_selected_body_start tops rpolicy
      (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) st /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    compile_entry_checks min_cds is_payable opened = ((),st) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_guarded_body cenv nr nkey ut' iv pbody rt sa = ((),st') /\
    fn_has_code ds de efn /\ fn_has_code opened st efn /\
    fn_has_code st sa efn /\ fn_has_code sa st' efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    cs_extends opened st /\
    de.cs_next_var <= opened.cs_next_var
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb_src,ctor)` >> fs[] >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  drule_all lower_vyper_runtime_legacy_packages >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `extpkgs = MAP (set_external_package_target rpolicy.rpol_target o
    package_external_fn tops T (K global_nonreentrant_slot)) exts` >>
  `MEM (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) extpkgs` by
    (simp[Abbr`extpkgs`, MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  `ALL_DISTINCT (MAP FST extpkgs)` by
    (drule external_names_distinct_numeric_namespace >>
     disch_then (mp_tac o MATCH_MP externalEntryChecksTheory.classified_external_labels_distinct) >>
     fs[Abbr`extpkgs`, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD,
          package_external_fn_def, set_external_package_target_def]) >>
  `~MEM lbl (MAP FST pre)` by
    (gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `runtime_selected_body_start tops rpolicy
     (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) sk` by
    (simp[runtime_selected_body_start_def] >>
     qexistsl_tac [`pre`, `post`, `before`, `sc`] >> fs[Abbr`extpkgs`]) >>
  `elbl = "__entry"` by
    (drule_all lower_vyper_runtime_unit_entry_label >> simp[]) >>
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sk`, `cenv`, `sa`, `sb`] >>
  simp[block_is_terminated_def]
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
  strip_tac >>
  `lowering_context_ok unit.cu_context` by
    (qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
     simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
     Cases_on `classify_functions tops` >> PairCases_on `r` >> simp[] >>
     strip_tac >> Cases_on `EXISTS external_has_defaults q` >> gvs[] >>
     imp_res_tac run_grouped_lowering_context >>
     imp_res_tac run_lowering_context_ok >> simp[]) >>
  pop_assum (mp_tac o MATCH_MP lowering_context_ok_static_integrity) >>
  strip_tac >> drule_all ctx_inst_ids_distinct_fn >>
  simp[fn_inst_ids_distinct_def, fn_insts_def,
    venomFnInstsProofsTheory.fn_insts_blocks_map_id]
QED

Theorem classified_entry_prefix_structure:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel NONE) tops)) /\
  MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,
     name,args,([] : expr list),ret,fbody)) (FST (classify_functions tops)) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (subst_consts_fn (module_consts_env tops [])
        (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,
         name,args,([] : expr list),ret,fbody))) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) ==>
  ?fb ds de opened st cenv sa st'.
    runtime_selected_body_start tops rpolicy
      (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) st /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    compile_entry_checks min_cds is_payable opened = ((),st) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_guarded_body cenv nr nkey ut' iv pbody rt sa = ((),st') /\
    fn_has_code ds de efn /\ fn_has_code opened st efn /\
    fn_has_code st sa efn /\ fn_has_code sa st' efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    cs_extends opened st /\
    de.cs_next_var <= opened.cs_next_var /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    cenv.ce_return_buf = NONE /\ fn_inst_ids_distinct efn
Proof
  strip_tac >> drule_all classified_entry_prefix_code >> strip_tac >>
  qpat_assum `set_external_package_target _ _ = _`
    (assume_tac o REWRITE_RULE [constSubstTheory.subst_consts_fn_def, MAP]) >>
  drule_all target_external_registration_locals >> strip_tac >>
  drule_all compile_entry_checks_open >> strip_tac >>
  drule_all compile_register_positional_args_open >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  drule_all lowered_runtime_function_inst_ids_distinct >> strip_tac >>
  qexistsl_tac [`fb`, `ds`, `de`, `opened`, `st`, `cenv`, `sa`, `st'`] >> simp[]
QED

Theorem source_selected_entry_prefix_structure_nr:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\ name <> "__default__" /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel NONE) tops)) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (subst_consts_fn (module_consts_env tops [])
        (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,
         name,args,([] : expr list),ret,fbody))) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) ==>
  ?fb ds de opened st cenv sa st'.
    runtime_selected_body_start tops rpolicy
      (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,pbody,rt) st /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    compile_entry_checks min_cds is_payable opened = ((),st) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_guarded_body cenv nr nkey ut' iv pbody rt sa = ((),st') /\
    fn_has_code ds de efn /\ fn_has_code opened st efn /\
    fn_has_code st sa efn /\ fn_has_code sa st' efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    cs_extends opened st /\
    de.cs_next_var <= opened.cs_next_var /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    cenv.ce_return_buf = NONE /\ fn_inst_ids_distinct efn
Proof
  strip_tac >>
  drule_all lookup_function_external_raw_member >> strip_tac >>
  drule_all_then ACCEPT_TAC classified_entry_prefix_structure
QED
