(* Connect successful linked calldata decoding to the installed entry route. *)
Theory dispatchedSelectionMods
Ancestors
  dispatchedMissSelectionMods dispatchedClassifiedRouteMods
  dispatchedSignatureOriginMods dispatchedSignatureLookupMods
  dispatchedClassifierMods dispatchedDecodedBindMods
  e2eModsDefs vyperInterpreter vyperTypeContract venomInst alist list

Theorem linked_dispatched_binding_route:
  source_typing_ok_mods mods exps am tx /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  ALOOKUP mods (ALOOKUP exps name) = SOME tops /\
  vyperInterpreter$lookup_function (ALOOKUP exps name) name External tops =
    SOME (mut,guarded,args,[],ret,fbody) /\
  calldata_dispatch_mods mods exps cd = SOME (name,vals) ==>
  (?env. bind_arguments (type_env_all_modules mods) args vals = SOME env) /\
  ((?rr b'. MEM (ALOOKUP exps name,(mut,guarded,rr,name,args,([]:expr list),ret,b')) exts /\
            !fl. linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
              (type_env_all_modules mods) (MAP SND exts))) fl = "fn_" ++ name) \/
   (?rr b'. fb = SOME (ALOOKUP exps name,(mut,guarded,rr, "__default__" ,[],([]:expr
     list),ret,b')) /\
            !fl. linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors
              (type_env_all_modules mods) (MAP SND exts))) fl = fl))
Proof
  simp[LET_THM] >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `LENGTH cd < 4 \/
    FIND (\(n,ts). abi_method_id (type_env_all_modules mods) n ts = cd_selector cd)
      (abi_deployed_signatures mods exps) = NONE`
  >- (drule_all (SRULE [LET_THM] linked_dispatched_miss_binding_route) >>
      metis_tac[]) >>
  fs[DE_MORGAN_THM] >>
  `?tys tvs.
      FIND (\(n,ts). abi_method_id (type_env_all_modules mods) n ts = cd_selector cd)
        (abi_deployed_signatures mods exps) = SOME (name,tys) /\
      OPT_MMAP (evaluate_type (type_env_all_modules mods)) tys = SOME tvs /\
      calldata_decode_args cd tvs 0 = SOME vals` by
    (Cases_on `FIND (\(n,ts). abi_method_id (type_env_all_modules mods) n ts = cd_selector cd)
       (abi_deployed_signatures mods exps)` >> fs[] >>
     rename1 `FIND _ _ = SOME sig` >> Cases_on `sig` >>
     qpat_x_assum `calldata_dispatch_mods _ _ _ = _` mp_tac >>
     simp[calldata_dispatch_mods_def,AllCaseEqs()] >> metis_tac[]) >>
  `MEM (name,tys) (abi_deployed_signatures mods exps)` by metis_tac[FIND_MEM] >>
  drule_all (SRULE [LET_THM] deployed_signature_selected_decl) >>
  disch_then (qx_choose_then `top` (CONJUNCTS_THEN assume_tac)) >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (ALOOKUP exps name)) tops))` by
    (fs[source_typing_ok_mods_def] >>
     metis_tac[ALOOKUP_MEM,check_contract_external_names_distinct,contract_keys_module_distinct]) >>
  drule_all selected_decl_lookup_args >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
  conj_tac >- metis_tac[decoded_parameters_bind] >>
  disj1_tac >>
  drule_all (SRULE [LET_THM] selected_external_member_mods) >>
  disch_then (qx_choose_then `rr` (qx_choose_then `b` assume_tac)) >>
  qexistsl_tac [`rr`,`b`] >> simp[] >>
  drule_all (SRULE [LET_THM] linked_classified_linear_routes) >>
  disch_then (qspec_then `cd` (mp_tac o CONJUNCT2)) >>
  `4 <= LENGTH cd` by decide_tac >> metis_tac[]
QED
