Theory entrySourcePackages
Ancestors
  entryValueRejectFacts loweringShapeProps loweringShapeDefs compileVyper compileEnv entryDispatchProps
  supportedProgram supportedNames supportedDecls e2eDefs list

Theorem selected_external_source_member[local]:
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?rr. MEM (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)
    (FST (classify_functions tops))
Proof
  strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  `!nr mut ty slot. ~MEM (VariableDecl (Public nr) mut tx.function_name ty slot) tops` by
    (fs[EVERY_MEM] >> metis_tac[supported_public_variables_rejected]) >>
  `!nr tr kt vt slot. ~MEM (HashMapDecl (Public nr) tr tx.function_name kt vt slot) tops` by
    (rpt strip_tac >> fs[EVERY_MEM] >>
     first_x_assum drule >> simp[supported_hashmap_header_contract]) >>
  `tx.function_name <> "__default__"` by gvs[valid_vyper_call_def] >>
  drule_all lookup_function_external_mem >> simp[]
QED

Theorem external_source_package_labels[local]:
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl)
    (MAP (set_external_package_target target o
      package_external_fn tops tr nk) exts)
Proof
  simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
       package_external_fn_def, set_external_package_target_def,
       jump_label_ok_def]
QED

Theorem internal_source_package_labels[local]:
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors
      (MAP (set_internal_package_target target o
        package_internal_fn tops tr nk F 0) ints))
Proof
  rewrite_tac[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
              internal_fn_descriptors_MAP_package_internal_fn] >>
  rw[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rewrite_tac[internal_label_ok_def, internal_fn_label_prefix]
QED

Theorem selected_external_package_member[local]:
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?ce pa mc key view rt.
    MEM ("fn_" ++ tx.function_name,ce,pa,mc,mut = Payable,nr,key,T,view,fbody,rt)
      (MAP (set_external_package_target target o
        package_external_fn tops T (K global_nonreentrant_slot))
        (FST (classify_functions tops)))
Proof
  strip_tac >> drule_all selected_external_source_member >> strip_tac >>
  `?ce pa mc key view rt.
     set_external_package_target target
       (package_external_fn tops T (K global_nonreentrant_slot)
         (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
       ("fn_" ++ tx.function_name,ce,pa,mc,mut = Payable,nr,key,T,view,fbody,rt)` by
    simp[package_external_fn_def, set_external_package_target_def] >>
  metis_tac[MEM_MAP, combinTheory.o_THM]
QED

Theorem lower_runtime_selected_source_packages:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?sels exts ints fb ei ce pa mc key view rt.
    run_lowering sels exts ints fb rp 0 0 [] ei "__entry" = SOME u /\
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
    MEM ("fn_" ++ tx.function_name,ce,pa,mc,mut = Payable,nr,key,T,view,fbody,rt) exts
Proof
  strip_tac >> drule_all selected_external_package_member >>
  disch_then (qspec_then `rp.rpol_target` strip_assume_tac) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> simp[] >>
  strip_tac >>
  `~EXISTS external_has_defaults q` by
    (drule supported_program_no_external_defaults >> simp[]) >>
  qpat_x_assum `(if EXISTS external_has_defaults q then _ else _) = _`
    mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> fs[] >>
  goal_assum (drule_at Any) >>
  simp[external_source_package_labels, internal_source_package_labels] >>
  metis_tac[]
QED
