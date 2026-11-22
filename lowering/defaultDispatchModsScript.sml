(* The default name may select a public getter or the actual fallback. *)
Theory defaultDispatchMods
Ancestors
  compileUnit constSubstMods e2eModsDefs entryRejectCode
  defaultDispatchModsFallback defaultDispatchModsGetter defaultDispatchModsHit
  defaultDispatchModsNames defaultDispatchModsPackage defaultDispatchModsRoute
  defaultDispatchModsRun defaultDispatchModsSignatures defaultDispatchModsSize
  vyperTypeContract entryLinearAppend entryCompileIntervals fragExec list pair option
  compileVyper compileEnv moduleLowering

Theorem default_dispatch_cases_mods:
  !sels. sels = MAP (\(sel,lbl,z). (sel,lbl))
               (build_selectors (type_env_all_modules mods) (MAP SND exts)) ==>
  !package. package = set_external_package_target rpolicy.rpol_target o
                package_external_fn_unit mods T (K global_nonreentrant_slot) ==>
  !body. body = subst_consts_stmts_mods (consts_env_mods mods) fbody ==>
  !decl.
    decl = (ALOOKUP exps tx.function_name,
            (mut,F,lookup_raw_return_or_F (ALOOKUP exps tx.function_name)
                     tx.function_name External tops,
             tx.function_name,args,([]:expr list),ret,body)) ==>
    classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    source_typing_ok_mods mods exps am tx /\
    ~EXISTS (external_has_defaults o SND) exts /\
    tx.function_name = "__default__" /\
    ALOOKUP mods (ALOOKUP exps tx.function_name) = SOME tops /\
    calldata_dispatch_mods mods exps cd = SOME (tx.function_name,vals) /\
    vyperInterpreter$lookup_function (ALOOKUP exps tx.function_name) tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME elbl ==>
    ?lbl ce pa mc pay key ut iv rt fallback label_st dispatch_st before checks
       st ce' body_st st'.
      package decl = (lbl,ce,pa,mc,pay,F,key,ut,iv,body,rt) /\
      fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
      compile_selector_dispatch_linear sels fallback label_st = ((),dispatch_st) /\
      new_block (linear_dispatch_target cd sels fallback) before =
        (before.cs_current_bb,checks) /\
      compile_entry_checks mc pay checks = ((),st) /\
      compile_register_positional_args ce pa 4 st = (ce',body_st) /\
      compile_guarded_body ce' F key ut iv body rt body_st = ((),st') /\
      cs_extends label_st dispatch_st /\ cs_extends dispatch_st checks /\
      cs_extends checks st /\ cs_extends st body_st /\ cs_extends body_st st' /\
      fn_has_code label_st dispatch_st func /\ fn_has_code checks st func /\
      fn_has_code st body_st func /\ fn_has_code body_st st' func /\
      label_st.cs_current_bb = elbl /\ label_st.cs_current_insts = [] /\
      label_st.cs_next_var = 0 /\
      ((linear_dispatch_target cd sels fallback = lbl /\
        (?tvs. OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND args) = SOME tvs /\
          mc = 4 + SUM (MAP tv_abi_size tvs) /\ mc <= LENGTH cd /\
          calldata_decode_args cd tvs 0 = SOME vals) /\
        ?pre post. MAP package exts = pre ++ package decl :: post /\
          ~MEM lbl (MAP FST pre) /\
          compile_external_fn_bodies pre dispatch_st = ((),before)) \/
       (args = [] /\ vals = [] /\ pa = [] /\ mc = 4 /\ ce.ce_vars = FEMPTY /\
        fb = SOME decl /\
        set_fallback_package_target rpolicy.rpol_target
          (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb) =
          SOME (ce,pay,F,key,ut,iv,body,rt) /\
        linear_dispatch_target cd sels fallback = fallback /\
        compile_external_fn_bodies (MAP package exts) dispatch_st = ((),before)))
Proof
  CONV_TAC (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV) >> strip_tac >>
  qpat_x_assum `tx.function_name = "__default__"` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors)` >>
  qabbrev_tac `src = ALOOKUP exps "__default__"` >>
  qabbrev_tac `stmts = subst_consts_stmts_mods (consts_env_mods mods) fbody` >>
  qabbrev_tac `decl = (src,(mut,F,lookup_raw_return_or_F src "__default__" External tops,
                      "__default__",args,([]:expr list),ret,stmts))` >>
  drule_all (SIMP_RULE pure_ss [LET_THM] default_unit_linear_run) >> strip_tac >>
  `elbl = "__entry"` by (drule_all run_lowering_entry_label >> simp[]) >>
  drule_then assume_tac (Q.INST [`name` |-> `"__default__"`]
    export_excludes_main_external) >>
  qabbrev_tac `tenv = type_env_all_modules mods` >>
  qabbrev_tac `sigs = abi_deployed_signatures mods exps` >>
  `ALL_DISTINCT (MAP (\(n,ts). abi_method_id tenv n ts) sigs)` by
    fs[Abbr `tenv`, Abbr `sigs`, source_typing_ok_mods_def, exports_ok_def] >>
  `!m n r name params ds res b.
     MEM (m,n,r,name,params,ds,res,b) (MAP SND exts) ==>
     MEM (name,MAP SND params) sigs` by
    (simp[Abbr `sigs`, MEM_MAP, EXISTS_PROD] >>
     metis_tac[compiled_entry_deployed_signature, tagged_getter_decl_signature]) >>
  drule_all (SIMP_RULE pure_ss [LET_THM] default_linear_routes) >>
  disch_then assume_tac >>
  qabbrev_tac `selectors = build_selectors tenv (MAP SND exts)` >>
  qabbrev_tac `sels = MAP (\(sel,lbl,z). (sel,lbl)) selectors` >>
  qpat_x_assum `calldata_dispatch_mods _ _ _ = _` mp_tac >>
  simp_tac pure_ss [calldata_dispatch_mods_def, LET_THM] >>
  simp_tac pure_ss [Abbr `tenv`, Abbr `sigs`] >>
  qabbrev_tac `hit = if LENGTH cd < 4 then NONE else
    FIND (\(n,ts). abi_method_id (type_env_all_modules mods) n ts = cd_selector cd)
      (abi_deployed_signatures mods exps)` >>
  Cases_on `hit`
  >- ((* Miss: the installed fallback has no argument registration interval. *)
      disch_tac >>
      `vals = [] /\ (EXISTS is_default_decl (main_module mods) \/
         IS_SOME (exported_fallback mods exps))` by fs[AllCaseEqs()] >>
      `args = [] /\ fb = SOME decl` by
        (fs[Abbr `decl`, Abbr `src`, Abbr `stmts`] >>
         metis_tac[default_miss_classified]) >>
      `!fl. linear_dispatch_target cd sels fl = fl` by
        (qpat_x_assum `Abbrev (NONE = _)` mp_tac >>
         simp[markerTheory.Abbrev_def, AllCaseEqs()] >> metis_tac[]) >>
      `?ce pay key ut iv rt.
        set_fallback_package_target rpolicy.rpol_target
          (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb) =
        SOME (ce,pay,F,key,ut,iv,stmts,rt)` by
        simp[Abbr `decl`, package_fallback_fn_unit_def, set_fallback_package_target_def] >>
      pop_assum strip_assume_tac >>
      `set_external_package_target rpolicy.rpol_target
         (package_external_fn_unit mods T (K global_nonreentrant_slot) decl) =
       ("fn___default__",ce,[],4,pay,F,key,ut,iv,stmts,rt) /\ ce.ce_vars = FEMPTY` by
        (qpat_x_assum `set_fallback_package_target _ _ = SOME _` mp_tac >>
         simp[Abbr `decl`] >> disch_then assume_tac >>
         drule empty_fallback_external_package_unit >> simp[]) >>
      qpat_assum `set_fallback_package_target _ _ = SOME _` (fn th =>
        qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _`
          (assume_tac o REWRITE_RULE [th])) >>
      drule_all run_lowering_fallback_interval_code >> strip_tac >>
      `fn_has_code st st func` by
        (qspecl_then [`st`,`st`,`se`,`func`] mp_tac fn_has_code_split >>
         simp[cs_extends_refl]) >>
      qexistsl [`"fn___default__"`,`ce`,`[]`,`4`,`pay`,`key`,`ut`,`iv`,`rt`,
                 `fl`,`sf`,`sd`,`opened`,`checks`,`st`,`ce`,`st`,`se`] >>
      simp[Abbr `sels`, compile_register_positional_args_def, comp_return_def,
           cs_extends_refl] >> metis_tac[]) >>
  (* Hit: identify the getter and its ABI width before locating its code. *)
  simp[AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `Abbrev (SOME _ = _)` mp_tac >>
  simp[markerTheory.Abbrev_def, AllCaseEqs()] >> strip_tac >>
  drule_then assume_tac venomInstTheory.FIND_MEM >>
  gvs[Abbr `src`] >>
  drule_all (SIMP_RULE pure_ss [LET_THM] default_signature_lookup_origin) >>
  strip_tac >>
  `abi_decl_signatures top = [("__default__", MAP SND args)] /\ MEM decl exts` by
    (gvs[Abbr `decl`, Abbr `stmts`] >>
     drule_all (Q.SPECL [`mods`,`exps`] selected_default_getter_classified) >>
     simp[subst_consts_fn_mods_def, subst_consts_expr_mods_def]) >>
  `tys = MAP SND args` by fs[] >> gvs[] >>
  `MEM (mut,F,F,"__default__",args,([]:expr list),ret,stmts) (MAP SND exts)` by
    (simp[MEM_MAP] >> qexists_tac `decl` >> simp[Abbr `decl`]) >>
  `4 <= LENGTH cd` by decide_tac >>
  `!fl. linear_dispatch_target cd sels fl = "fn___default__"` by
    (gen_tac >>
     qpat_assum `!fl data. _` (qspecl_then [`fl`,`cd`] (mp_tac o CONJUNCT2)) >>
     metis_tac[]) >>
  `?ce pa mc pay key ut iv rt. set_external_package_target rpolicy.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot) decl) =
    ("fn___default__",ce,pa,mc,pay,F,key,ut,iv,stmts,rt)` by
    simp[Abbr `decl`, package_external_fn_unit_def, set_external_package_target_def] >>
  pop_assum strip_assume_tac >>
  `MEM ("__default__",MAP SND args) (abi_decl_signatures top)` by simp[] >>
  `mc = 4 + SUM (MAP tv_abi_size tvs)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[Abbr `decl`] >> disch_then assume_tac >>
     drule_all default_getter_package_min_size >> simp[]) >>
  qabbrev_tac `extpkgs = MAP (set_external_package_target rpolicy.rpol_target o
                      package_external_fn_unit mods T (K global_nonreentrant_slot)) exts` >>
  `MEM ("fn___default__",ce,pa,mc,pay,F,key,ut,iv,stmts,rt) extpkgs` by
    (simp[Abbr `extpkgs`, MEM_MAP] >> qexists_tac `decl` >> simp[]) >>
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  `ALL_DISTINCT (MAP FST extpkgs)` by
    (drule_all linked_package_labels_distinct >> simp[Abbr `extpkgs`]) >>
  `~MEM "fn___default__" (MAP FST pre)` by
    (qpat_x_assum `ALL_DISTINCT (MAP FST extpkgs)` mp_tac >>
     simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_guarded_body) >>
  qexistsl [`"fn___default__"`,`ce`,`pa`,`mc`,`pay`,`key`,`ut`,`iv`,`rt`,
             `fl`,`sf`,`sd`,`before`,`sc`,`sk`,`cenv`,`sa`,`sb`] >>
  simp[Abbr `sels`] >> disj1_tac >> qexistsl [`pre`,`post`] >> simp[]
QED
