Theory entrySourcePackages
Ancestors
  entryValueRejectFacts loweringShapeProps loweringShapeDefs compileVyper compileEnv entryDispatchProps
  supportedProgram supportedNames supportedDecls e2eDefs list

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

Theorem lower_runtime_default_free_packages:
  lower_vyper_runtime_unit tops rp = SOME u /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) ==>
  ?sels exts ints fb ei.
    run_lowering sels exts ints fb rp 0 0 [] ei "__entry" = SOME u /\
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    exts = MAP (set_external_package_target rp.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot))
      (FST (classify_functions tops)) /\
    fb = set_fallback_package_target rp.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot)
        (FST (SND (SND (classify_functions tops))))) /\
    EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints)
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  simp[] >> strip_tac >>
  `~EXISTS external_has_defaults exts` by
    (qpat_assum `~EXISTS external_has_defaults _` mp_tac >>
     REWRITE_TAC [pairTheory.FST]) >>
  qpat_x_assum `(if EXISTS external_has_defaults exts then _ else _) = _`
    mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  simp[external_source_package_labels, internal_source_package_labels]
QED

Theorem selected_external_package_member[local]:
  supported_program tops /\ tx.function_name <> "__default__" /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?ce pa mc key view rt.
    MEM ("fn_" ++ tx.function_name,ce,pa,mc,mut = Payable,nr,key,T,view,
      subst_consts_stmts (module_consts_env tops []) fbody,rt)
      (MAP (set_external_package_target target o
        package_external_fn tops T (K global_nonreentrant_slot))
        (FST (classify_functions tops)))
Proof
  strip_tac >> drule_all lookup_function_external_member >> strip_tac >>
  `?ce pa mc key view rt.
     set_external_package_target target
       (package_external_fn tops T (K global_nonreentrant_slot)
         (subst_consts_fn (module_consts_env tops [])
           (mut,nr,rr,tx.function_name,args,dflts,ret,fbody))) =
       ("fn_" ++ tx.function_name,ce,pa,mc,mut = Payable,nr,key,T,view,
        subst_consts_stmts (module_consts_env tops []) fbody,rt)` by
    simp[package_external_fn_def, set_external_package_target_def,
         constSubstTheory.subst_consts_fn_def] >>
  qexistsl_tac [`ce`, `pa`, `mc`, `key`, `view`, `rt`] >> simp[MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem lower_runtime_named_source_packages:
  lower_vyper_runtime_unit tops rp = SOME u /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  tx.function_name <> "__default__" /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?sels exts ints fb ei ce pa mc key view rt.
    run_lowering sels exts ints fb rp 0 0 [] ei "__entry" = SOME u /\
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
    MEM ("fn_" ++ tx.function_name,ce,pa,mc,mut = Payable,nr,key,T,view,
      subst_consts_stmts (module_consts_env tops []) fbody,rt) exts /\
    exts = MAP (set_external_package_target rp.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot))
      (FST (classify_functions tops))
Proof
  strip_tac >> drule_all selected_external_package_member >>
  disch_then (qspec_then `rp.rpol_target` strip_assume_tac) >>
  drule_all lower_runtime_default_free_packages >> strip_tac >>
  qexistsl_tac [`sels`, `exts`, `ints`, `fb`, `ei`, `ce`, `pa`, `mc`,
                `key`, `view`, `rt`] >> fs[]
QED
