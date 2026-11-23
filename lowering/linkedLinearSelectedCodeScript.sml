(* Installed intervals of a selected external entry in a linked linear runtime. *)
Theory linkedLinearSelectedCode
Ancestors
  defaultDispatchModsRun entryRejectCode entryDispatchProps compileUnit
  compileVyper compileEnv vyperCompiler venomInst venomInstIdsProps fragExec context list pair

Theorem linked_linear_selected_registration_code:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  ~EXISTS (external_has_defaults o SND) exts /\
  MEM (src,(mut,nr,rr,name,args,[],ret,body_code)) exts /\
  set_external_package_target rp.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,(mut,nr,rr,name,args,[],ret,body_code))) =
    (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt) ==>
  ?fn fl ds de opened checked registered_env registered last.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__entry" /\ fn_inst_ids_distinct fn /\
    compile_selector_dispatch_linear
      (MAP (\(sel,l,z). (sel,l))
        (build_selectors (type_env_all_modules mods) (MAP SND exts)))
      fl ds = ((),de) /\
    fn_has_code ds de fn /\ cs_extends de opened /\
    ds.cs_current_bb = "__entry" /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    opened.cs_current_bb = lbl /\ opened.cs_current_insts = [] /\
    ~block_is_terminated opened /\
    compile_entry_checks mc pay opened = ((),checked) /\
    compile_register_positional_args ce pos 4 checked = (registered_env,registered) /\
    compile_guarded_body registered_env nr key tr view body_code rt registered = ((),last) /\
    fn_has_code opened checked fn /\ fn_has_code checked registered fn /\
    fn_has_code registered last fn /\ cs_extends opened checked /\ cs_extends checked registered
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE pure_ss [LET_THM] default_unit_linear_run) >>
  disch_then (qx_choose_then `ips` strip_assume_tac) >>
  drule run_lowering_entry >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `fn` assume_tac)) >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all_then ACCEPT_TAC run_lowering_entry_label) >>
  `MEM (lbl,ce,pos,mc,pay,nr,key,tr,view,body_code,rt)
      (MAP (set_external_package_target rp.rpol_target o
        package_external_fn_unit mods T (K global_nonreentrant_slot)) exts)` by
    (simp[MEM_MAP] >>
     qexists_tac `(src,(mut,nr,rr,name,args,[],ret,body_code))` >>
     simp[] >>
     qpat_assum `set_external_package_target _ _ = _`
       (mp_tac o SYM) >>
     PURE_REWRITE_TAC [package_external_fn_unit_def, LENGTH] >>
     disch_then ACCEPT_TAC) >>
  drule_all run_lowering_selected_entry_code >>
  disch_then (qx_choosel_then [`fl`,`ds`,`de`,`opened`,`checked`,
    `registered_env`,`registered`,`last`] strip_assume_tac) >>
  qexistsl_tac [`fn`,`fl`,`ds`,`de`,`opened`,`checked`,
    `registered_env`,`registered`,`last`] >>
  fs[block_is_terminated_def]
QED
