(* A successful selector miss selects the stored, zero-parameter fallback. *)
Theory dispatchedMissSelectionMods
Ancestors
  dispatchedClassifiedRouteMods defaultDispatchModsFallback defaultDispatchModsNames
  e2eModsDefs vyperInterpreter

Theorem linked_dispatched_miss_binding_route:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\
  vyperInterpreter$lookup_function (ALOOKUP exps name) name External tops =
    SOME (mut,guarded,args,[],ret,fbody) /\
  calldata_dispatch_mods mods exps cd = SOME (name,vals) /\
  (LENGTH cd < 4 \/ FIND (\(n,ts). abi_method_id (type_env_all_modules mods) n ts = cd_selector
    cd) (abi_deployed_signatures mods exps) = NONE) ==>
  (?env. bind_arguments (type_env_all_modules mods) args vals = SOME env) /\
  (?rr b'. fb = SOME (ALOOKUP exps name,(mut,guarded,rr, "__default__" ,[],([]:expr
    list),ret,b')) /\
           !fl. linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
             (type_env_all_modules mods) (MAP SND exts))) fl = fl)
Proof
  simp[LET_THM] >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!fl. linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors (type_env_all_modules mods) (MAP SND exts))) fl = fl` by
    (drule_all (SRULE [LET_THM] linked_classified_linear_routes) >>
     disch_then (qspec_then `cd` (mp_tac o CONJUNCT1)) >> simp[]) >>
  `(if LENGTH cd < 4 then NONE else
      FIND (\(n,ts). abi_method_id (type_env_all_modules mods) n ts = cd_selector cd)
        (abi_deployed_signatures mods exps)) = NONE` by
    (IF_CASES_TAC >> fs[]) >>
  qpat_x_assum `calldata_dispatch_mods _ _ _ = _` mp_tac >>
  simp[calldata_dispatch_mods_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `name = _` SUBST_ALL_TAC >>
  drule (SIMP_RULE std_ss [AND_IMP_INTRO] export_excludes_main_external) >>
  disch_then (qspec_then `"__default__"` assume_tac) >>
  (* The key namespace in the exclusion clause is polymorphic. *)
  mp_tac (Q.INST [`imp_ctors` |-> `ics`]
    (INST_TYPE [``:'a`` |-> ``:num``] default_miss_classified)) >>
  asm_simp_tac std_ss [LET_THM,bind_arguments_def]
QED
