(* Resolve calls of a typed statement at the linked unit's active module. *)
Theory bodyActiveStmtCallsMods
Ancestors
  bodyLinkedCallResolution bodyFullPredsMods bodyInvModuleProps
  bodyExprPreFacts supportedStmtTraverse exprSimHypsDefs
  whitelistCheckerDecls list pair

Theorem active_calls_resolve_mods[local]:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  EVERY (\c. c IN FDOM env.fn_sigs) calls /\
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) calls ==>
  EVERY (source_body_call_supported cx) calls
Proof
  strip_tac >>
  drule_then assume_tac module_body_inv_lookup >>
  `linked_fn_sigs_declared mods cx env.fn_sigs` by fs[expr_sim_inv_mods_def] >>
  `?art. check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art` by
    (qpat_assum `body_const_cells_agree_mods _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     goal_assum drule) >>
  pop_assum strip_assume_tac >>
  `EVERY (\c. FST c = NONE ==>
              IS_SOME (supported_function_decl (main_module mods) c Internal)) calls` by
    (fs[EVERY_MEM, FORALL_PROD] >>
     qx_gen_tac `name` >> strip_tac >>
     `(NONE,name) IN FDOM env.fn_sigs` by (first_x_assum irule >> simp[]) >>
     `IS_SOME (supported_function_decl tops (NONE,name) Internal)` by
       (first_x_assum irule >> simp[]) >>
     drule_all_then ACCEPT_TAC checked_linked_unqualified_call) >>
  drule_all_then ACCEPT_TAC supported_body_calls_resolve
QED

Theorem active_stmt_calls_resolve_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es ==>
  (!bindings s ret env'. supported_stmt tops bindings s /\
     type_stmt env ret s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) /\
  (!bindings ss ret env'. supported_stmts tops bindings ss /\
     type_stmts env ret ss = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmts ss))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      drule_then assume_tac supported_stmt_body_safe >>
      drule_then assume_tac (cj 1 type_stmt_int_calls_fn_sigs) >>
      fs[body_stmt_safe_def] >>
      drule_all_then ACCEPT_TAC active_calls_resolve_mods) >>
  rpt strip_tac >>
  drule_then assume_tac supported_stmts_body_safe >>
  drule_then assume_tac (cj 2 type_stmt_int_calls_fn_sigs) >>
  fs[body_stmts_safe_iff] >>
  drule_all_then ACCEPT_TAC active_calls_resolve_mods
QED
