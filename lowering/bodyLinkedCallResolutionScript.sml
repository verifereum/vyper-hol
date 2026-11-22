(* Link checked call signatures to source declarations, including deploy entries. *)
Theory bodyLinkedCallResolution
Ancestors
  bodyCallSupport bodyInvSplit bodyMainModuleProps bodyInvCodeProps
  exprSimHypsDefs supportedDecls supportedProgram vyperTypeContract
  vyperTypeCallGraph vyperTypeInvariants alist finite_map list pair

Theorem supported_body_calls_resolve:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  EVERY (\c. c IN FDOM env.fn_sigs) calls /\
  EVERY (\c. FST c = NONE ==>
    IS_SOME (supported_function_decl (main_module mods) c Internal)) calls ==>
  EVERY (source_body_call_supported cx) calls
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_main_module >>
  drule_then assume_tac contract_inv_module_codes >>
  `fn_sigs_consistent env.fn_sigs cx /\ fn_sigs_live env.fn_sigs cx /\
    linked_fn_sigs_declared mods cx env.fn_sigs` by
    fs[expr_sim_inv_mods_def, env_consistent_def, env_context_consistent_def] >>
  fs[EVERY_MEM, pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`src`, `name`] >> strip_tac >>
  Cases_on `src`
  >- (simp[source_body_call_supported_def, supported_linked_callee_def] >>
      fs[contract_inv_def] >> res_tac >> simp[]) >>
  `?sig. FLOOKUP env.fn_sigs (SOME x,name) = SOME sig` by
    (res_tac >> gvs[FLOOKUP_DEF]) >>
  pop_assum strip_assume_tac >>
  `?tops. ALOOKUP mods (SOME x) = SOME tops` by
    (fs[fn_sigs_consistent_def] >> res_tac >> gvs[]) >>
  `!ts. mods <> [(NONE,ts)]` by
    (rpt strip_tac >> gvs[ALOOKUP_def]) >>
  `context_function_live cx (SOME x,name)` by
    fs[fn_sigs_live_def] >>
  fs[linked_fn_sigs_declared_def] >>
  res_tac >> gvs[] >>
  simp[source_body_call_supported_def, supported_linked_callee_def] >>
  fs[contract_inv_def] >> res_tac >> simp[] >>
  conj_tac
  >- (Cases_on `vis` >> gvs[include_fn_sig_def] >>
      metis_tac[supported_function_decl_exists]) >>
  qexistsl [`vis`, `raw`] >> simp[]
QED

Theorem linked_body_calls_resolve:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  (!ts. mods <> [(NONE,ts)]) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  context_function_live cx (src,name) /\
  check_function_body_in_mode cx.in_deploy vis /\
  EVERY (\call. call IN FDOM env.fn_sigs /\
    MEM call (function_int_calls dflts ss)) calls ==>
  EVERY (source_body_call_supported cx) calls
Proof
  strip_tac >>
  `EVERY (\c. c IN FDOM env.fn_sigs) calls` by
    fs[EVERY_MEM] >>
  drule_then assume_tac contract_inv_main_module >>
  `linked_body_calls_resolved mods cx` by fs[contract_inv_def] >>
  `EVERY (\call. ?callee.
      ALOOKUP mods (FST call) = SOME callee /\
      supported_linked_callee cx.in_deploy callee call)
      (function_int_calls dflts ss)` by
    (fs[linked_body_calls_resolved_def] >> res_tac) >>
  `EVERY (\c. FST c = NONE ==>
      IS_SOME (supported_function_decl (main_module mods) c Internal)) calls` by
    (fs[EVERY_MEM, FORALL_PROD, supported_linked_callee_def] >>
     metis_tac[optionTheory.SOME_11]) >>
  metis_tac[supported_body_calls_resolve]
QED
