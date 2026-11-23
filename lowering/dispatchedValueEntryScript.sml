(* Ordinary entry checks depend on classified membership, not source names. *)
Theory dispatchedValueEntry
Ancestors entryRejectCode compileVyper moduleLowering supportedProgram
  compileEnv vyperCompiler venomInst emitHelper placeMemoryCodeLayout list

Theorem source_member_entry_check_code_nr:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  MEM (mut,nr,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
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
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb_src,ctor)` >>
  fs[] >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  drule_all lower_vyper_runtime_legacy_packages >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  `elbl = "__entry"` by
    (drule_all lower_vyper_runtime_unit_entry_label >> simp[]) >>
  qabbrev_tac `pack = set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,name,args,([]:expr list),ret,fbody))` >>
  PairCases_on `pack` >>
  `pack0 = "fn_" ++ name /\ pack4 = (mut = Payable)` by
    (qpat_x_assum `Abbrev _` mp_tac >>
     simp[markerTheory.Abbrev_def, package_external_fn_def, set_external_package_target_def]) >>
  `MEM (pack0,pack1,pack2,pack3,pack4,pack5,pack6,pack7,pack8,pack9,pack10)
    (MAP (set_external_package_target rpolicy.rpol_target o
          package_external_fn tops T (K global_nonreentrant_slot)) exts)` by
    (qpat_assum `Abbrev _` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[MEM_MAP] >>
     qexists_tac `(mut,nr,rr,name,args,([]:expr list),ret,fbody)` >> simp[]) >>
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  `sf.cs_next_var = 0` by
    (drule fresh_label_next_var >> simp[initial_compile_state_def]) >>
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sk`, `pack3`] >>
  gvs[block_is_terminated_def]
QED
