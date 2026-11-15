(* Ordinary entry checks depend on classified membership, not source names. *)
Theory dispatchedValueEntry
Ancestors runtimeExternalPackageCode entryCheckIntervals compileVyper
  actualDecoderPackaging moduleLowering supportedProgram list

Theorem source_member_entry_check_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  MEM (mut,F,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
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
  strip_tac >> drule_all source_runtime_external_packages >> strip_tac >>
  `MEM (set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,rr,name,args,([] : expr list),ret,fbody))) extpkgs` by
    (simp_tac pure_ss [Once EQ_SYM_EQ] >>
     qpat_x_assum `extpkgs = _` (fn th => rewrite_tac[th]) >>
     simp[MEM_MAP] >>
     qexists_tac `(mut,F,rr,name,args,([] : expr list),ret,fbody)` >> simp[]) >>
  pop_assum mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  strip_tac >> gvs[] >>
  drule_all installed_selected_check_code >> strip_tac >>
  qexistsl_tac [`fallback`, `label_st`, `dispatch_st`, `opened`, `checked`] >>
  simp[] >> goal_assum (drule_at Any)
QED
