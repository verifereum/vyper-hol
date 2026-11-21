(* Install the rejecting prefix from the classified fallback package. *)
Theory dispatchedValueFallback
Ancestors entryRejectCode compileVyper moduleLowering supportedProgram
  compileEnv vyperCompiler venomInst emitHelper list

Theorem source_fallback_entry_check_code_nr:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,"__default__",args,[],ret,fbody) /\
  mut <> Payable /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?fb ds de opened checked.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    fn_has_code ds de efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    compile_entry_checks 0 F opened = ((),checked) /\
    fn_has_code opened checked efn /\ opened.cs_current_bb = fb /\
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
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  strip_tac >>
  drule_all run_lowering_fallback_check_code >> strip_tac >>
  qexistsl_tac [`sf`, `sd`, `sc`, `sk`] >>
  gvs[block_is_terminated_def]
QED
