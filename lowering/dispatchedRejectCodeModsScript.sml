(* Locate the installed nonpayable check in a default-free linked runtime. *)
Theory dispatchedRejectCodeMods
Ancestors
  defaultDispatchModsRun entryDispatchProps entryRejectCode e2eModsDefs
  compileUnit compileVyper compileEnv vyperCompiler venomInst fragExec list pair

Theorem linked_routed_reject_code:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  source_typing_ok_mods mods exps am tx /\
  ~EXISTS (external_has_defaults o SND) exts /\
  mut <> Payable /\
  ((?rr body. MEM (src,(mut,nr,rr,name,args,[],ret,body)) exts /\
              !fl. (linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
                (type_env_all_modules mods) (MAP SND exts)))) fl = "fn_" ++ name) \/
   (?rr body. fb = SOME (src,(mut,nr,rr,"__default__",[],[],ret,body)) /\
              !fl. (linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
                (type_env_all_modules mods) (MAP SND exts)))) fl = fl)) ==>
  ?fn selectors fl ds de opened checked mc.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__entry" /\
    EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
    compile_selector_dispatch_linear selectors fl ds = ((),de) /\
    fn_has_code ds de fn /\
    ds.cs_current_bb = "__entry" /\ ds.cs_current_insts = [] /\
    compile_entry_checks mc F opened = ((),checked) /\
    fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    opened.cs_current_bb = linear_dispatch_target cd selectors fl
Proof
  simp_tac pure_ss [LET_THM] >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> disch_tac >>
  drule_all (SIMP_RULE pure_ss [LET_THM] default_unit_linear_run) >> strip_tac >>
  drule run_lowering_entry >> strip_tac >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all_then ACCEPT_TAC run_lowering_entry_label) >>
  qabbrev_tac `sels = build_selectors (type_env_all_modules mods) (MAP SND exts)` >>
  qabbrev_tac `packs = MAP (set_external_package_target rp.rpol_target o
    package_external_fn_unit mods T (K global_nonreentrant_slot)) exts` >>
  `EVERY (\(sel,lbl). sel < 2 ** 32) (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    simp[Abbr `sels`, linear_selectors_lt] >>
  qexistsl_tac [`fn`, `MAP (\(sel,lbl,z). (sel,lbl)) sels`] >>
  qpat_x_assum `(?rr body. MEM _ _ /\ _) \/ _` strip_assume_tac
  >- (rename1 `MEM (src,(mut,nr,rret,name,args,[],ret,body_code)) exts` >>
      qabbrev_tac `pack = set_external_package_target rp.rpol_target
        (package_external_fn_unit mods T (K global_nonreentrant_slot)
          (src,(mut,nr,rret,name,args,([]:expr list),ret,body_code)))` >>
      `MEM pack packs` by
        (simp[Abbr `packs`, Abbr `pack`, MEM_MAP] >>
         qexists_tac `(src,(mut,nr,rret,name,args,[],ret,body_code))` >> simp[]) >>
      PairCases_on `pack` >>
      `pack0 = "fn_" ++ name /\ pack4 = F` by
        (qpat_x_assum `Abbrev ((pack0,_) = _)` mp_tac >>
         simp[markerTheory.Abbrev_def, package_external_fn_unit_def,
              set_external_package_target_def]) >>
      drule_all run_lowering_selected_entry_code >> strip_tac >>
      qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sk`, `pack3`] >>
      gvs[block_is_terminated_def]) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[package_fallback_fn_unit_def, set_fallback_package_target_def] >> strip_tac >>
  drule_all run_lowering_fallback_check_code >> strip_tac >>
  qexistsl_tac [`sf`, `sd`, `sc`, `sk`, `0`] >>
  gvs[block_is_terminated_def]
QED
