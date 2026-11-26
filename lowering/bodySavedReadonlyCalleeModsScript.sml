(* The runtime artifact excludes deploy constructors even during deployment. *)
Theory bodySavedReadonlyCalleeMods
Ancestors
  bodyInvCodeProps bodyInvSplit constSubstCorrect whitelistCheckerDecls
  vyperReadOnlyEval vyperReadOnlySyntax vyperInterpreter
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeCallGraphSoundness
  vyperTypeCallGraph vyperContext vyperTypeSystem vyperTypeEvalProofs finite_map list rich_list alist

val _ = Parse.hide "body";

Triviality saved_readonly_callee_runtime_lookup:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  lookup_callable_function mode name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  (mut = View \/ mut = Pure) ==>
  lookup_callable_function F name tops = SOME (mut,nr,args,dflts,ret,ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `mode` >> fs[] >>
  drule_then strip_assume_tac lookup_callable_function_T_SOME_cases >>
  gvs[vyperASTTheory.function_mutability_distinct] >>
  FIRST [
    drule_then strip_assume_tac check_contract_artifact_fields >>
    drule_then assume_tac ALOOKUP_MEM >>
    drule_all_then assume_tac contract_namespaces_ok_module_fn_sig_keys >>
    drule_all_then ACCEPT_TAC lookup_function_Internal_MEM,
    drule_all_then mp_tac checked_function_mutability >>
    simp[function_mutability_ok_def]]
QED

Triviality saved_readonly_callee_runtime_sig:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  ALOOKUP mods src = SOME tops /\
  MEM (src,name) (linked_live_functions mods exps) /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  (mut = View \/ mut = Pure) ==>
  IS_SOME (FLOOKUP art.cta_fn_sigs (src,name))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac saved_readonly_callee_runtime_lookup >>
  drule_all_then assume_tac linked_live_functions_function_live >>
  drule_then strip_assume_tac check_contract_artifact_fields >>
  drule_all_then assume_tac build_contract_type_artifact_fn_sigs_complete >>
  fs[optionTheory.IS_SOME_EXISTS, FLOOKUP_DRESTRICT_SOME]
QED

Triviality saved_readonly_nested_runtime_sigs:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  IS_SOME (FLOOKUP art.cta_fn_sigs (src,name)) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function mode name ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  EVERY (\k. IS_SOME (FLOOKUP art.cta_fn_sigs k)) (int_calls_exprs dflts) /\
  EVERY (\k. IS_SOME (FLOOKUP art.cta_fn_sigs k)) (int_calls_stmts ss)
Proof
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule_all checked_callable_body_typing >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule_then assume_tac (cj 2 type_stmt_int_calls_fn_sigs) >>
  drule_then assume_tac (cj 4 well_typed_int_calls_fn_sigs) >>
  fs[function_entry_env_fn_sigs, defaults_env_def, EVERY_MEM, FLOOKUP_DEF]
QED

Theorem saved_readonly_callee_frames_checked_mods:
  contract_inv mods exps ctx cenv cx /\
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (src,name) (linked_live_functions mods exps) /\ (mut = View \/ mut = Pure) ==>
  !f n.
    state_rel_frame machine_frame (eval_exprs (cx with stk updated_by f) (DROP n dflts)) /\
    state_rel_frame machine_frame (eval_stmts (cx with stk updated_by f) ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac contract_inv_module_codes >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods` by fs[contract_inv_def] >>
  `ALOOKUP mods src = SOME tops` by fs[] >>
  drule_all_then assume_tac saved_readonly_callee_runtime_sig >>
  drule_all_then assume_tac saved_readonly_callee_runtime_lookup >>
  `EVERY (expr_mutability_ok mods View) dflts /\ stmts_mutability_ok mods View ss` by
    metis_tac[checked_internal_read_only] >>
  drule_all_then strip_assume_tac saved_readonly_nested_runtime_sigs >>
  qspecl_then [`get_module_code cx`, `cx.in_deploy`, `mods`,
               `\k. IS_SOME (FLOOKUP art.cta_fn_sigs k)`]
    (mp_tac o BETA_RULE) evaluate_read_only_calls >>
  impl_tac
  >- (map_every qx_gen_tac [`s`, `fn`, `ts`] >> strip_tac >>
      `ALOOKUP mods s = SOME ts` by
        (qpat_assum `!k. get_module_code cx k = ALOOKUP mods k`
           (qspec_then `s` (once_rewrite_tac o single o SYM)) >>
         first_assum ACCEPT_TAC) >>
      `lookup_callable_function cx.in_deploy fn ts = lookup_callable_function F fn ts` by
        metis_tac[checked_signature_callable_mode, optionTheory.IS_SOME_EXISTS] >>
      simp[] >> map_every qx_gen_tac [`fm`, `locked`, `formals`, `defaults`, `rty`, `code`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      conj_tac >- metis_tac[checked_internal_read_only] >>
      conj_tac >- metis_tac[checked_internal_read_only] >>
      metis_tac[saved_readonly_nested_runtime_sigs]) >>
  strip_tac >> rpt gen_tac >> conj_tac >> first_assum irule >>
  fs[int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP, EVERY_DROP,
     FUN_EQ_THM, get_module_code_stk_irrelevant]
QED

Theorem saved_readonly_callee_syntax_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (src,name) (linked_live_functions mods exps) /\ (mut = View \/ mut = Pure) ==>
  EVERY (expr_mutability_ok mods View) dflts /\ stmts_mutability_ok mods View ss /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (function_int_calls dflts ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qspec_then `src` assume_tac) contract_inv_module_codes >>
  `?vis raw. MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops` by
    (Cases_on `cx.in_deploy` >> fs[] >>
     metis_tac[lookup_callable_function_T_SOME_cases, lookup_callable_function_F_SOME_MEM,
               vyperASTTheory.function_mutability_distinct]) >>
  `ALOOKUP mods src = SOME tops` by fs[] >>
  `function_mutability_ok mods vis mut nr dflts ss` by
    (qpat_x_assum `contract_inv _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [contract_inv_def]) >>
     qpat_assum `!a b c d e f g h i j k. _ ==> function_mutability_ok _ _ _ _ _ _ /\ _`
       (drule_then drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[]) >>
  conj_tac
  >- (fs[function_mutability_ok_def, EVERY_MEM] >>
      metis_tac[cj 1 expr_target_mutability_view]) >>
  conj_tac
  >- (fs[function_mutability_ok_def] >> metis_tac[stmt_mutability_view]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (src,tops) mods` by metis_tac[ALOOKUP_MEM] >>
  drule_all contract_call_edges_function >> strip_tac >>
  pure_rewrite_tac [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
  BETA_TAC >> irule (cj 2 call_closure_from_roots) >> qexists `src,name` >>
  qpat_assum `MEM (src,name) (linked_live_functions _ _)` mp_tac >>
  pure_rewrite_tac [linked_live_functions_def, linked_live_functions_from_def, LET_THM] >>
  simp[call_edge_rel_def]
QED

Theorem saved_readonly_callee_frames_mode_agree_mods:
  contract_inv mods exps ctx cenv cx /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (src,name) (linked_live_functions mods exps) /\ (mut = View \/ mut = Pure) /\
  (!src fn ts. MEM (src,fn) (linked_live_functions mods exps) /\
     get_module_code cx src = SOME ts ==>
     lookup_callable_function cx.in_deploy fn ts = lookup_callable_function F fn ts) ==>
  !f n.
    state_rel_frame machine_frame (eval_exprs (cx with stk updated_by f) (DROP n dflts)) /\
    state_rel_frame machine_frame (eval_stmts (cx with stk updated_by f) ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac contract_inv_module_codes >>
  drule_all_then strip_assume_tac saved_readonly_callee_syntax_mods >>
  qspecl_then [`get_module_code cx`, `cx.in_deploy`, `mods`,
               `\k. MEM k (linked_live_functions mods exps)`]
    (mp_tac o BETA_RULE) evaluate_read_only_calls >>
  impl_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all saved_readonly_callee_syntax_mods >> simp[function_int_calls_def, EVERY_APPEND]) >>
  strip_tac >> rpt gen_tac >> conj_tac >> first_assum irule >>
  fs[function_int_calls_def, EVERY_APPEND, int_calls_exprs_FLAT_MAP, EVERY_FLAT,
     EVERY_MAP, EVERY_DROP, FUN_EQ_THM, get_module_code_stk_irrelevant]
QED
