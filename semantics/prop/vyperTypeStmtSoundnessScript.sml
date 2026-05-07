(*
 * Statement and statement-list type soundness skeleton for the fresh executable
 * Vyper type system.
 *)

Theory vyperTypeStmtSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeEnv vyperTypeEnvPreservation vyperTypeBuiltins vyperTypeExprSoundness
  vyperStatePreservation vyperTypeStatePreservation
Libs
  wordsLib

(* ===== Exception/result typing ===== *)

Definition return_exception_typed_def:
  return_exception_typed env ret_ty exn <=>
    case exn of
    | ReturnException v => value_runtime_typed env ret_ty v
    | _ => T
End

Definition stmt_error_ok_def:
  stmt_error_ok env ret_ty r <=>
    no_type_error_result r /\
    (case r of INR exn => return_exception_typed env ret_ty exn | _ => T)
End

(* ===== Environment threading facts for executable statement typing ===== *)

Theorem extend_local_preserves_static:
  (extend_local env id ty assignable).type_defs = env.type_defs /\
  (extend_local env id ty assignable).current_src = env.current_src /\
  (extend_local env id ty assignable).fn_sigs = env.fn_sigs /\
  (extend_local env id ty assignable).bare_globals = env.bare_globals /\
  (extend_local env id ty assignable).toplevel_vtypes = env.toplevel_vtypes /\
  (extend_local env id ty assignable).flag_members = env.flag_members
Proof
  simp[extend_local_def]
QED

Theorem type_stmt_env_preserved_static:
  type_stmt env ret_ty s = SOME env' ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  Cases_on `s` >>
  rw[type_stmt_def, AllCaseEqs(), extend_local_def] >>
  gvs[oneline type_stmt_def, AllCaseEqs()]
QED

Theorem type_stmts_env_preserved_static:
  type_stmts env ret_ty ss = SOME env' ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  qid_spec_tac `env` >> Induct_on `ss` >>
  rw[type_stmt_def] >>
  gvs[type_stmt_def, AllCaseEqs()] >>
  drule type_stmt_env_preserved_static >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[]
QED

Theorem type_stmt_env_consistent_preserved_static:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  metis_tac[type_stmt_env_preserved_static]
QED

Theorem type_stmts_env_consistent_preserved_static:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st ==>
  env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
  env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
  env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members
Proof
  metis_tac[type_stmts_env_preserved_static]
QED

Theorem AnnAssign_env_consistent_after_new_variable:
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx (AnnAssign id typ e) st = (INL u, st') ==>
  env_consistent env' cx st' /\ state_well_typed st'
Proof
  rw[type_stmt_def] >> gvs[AllCaseEqs(), extend_local_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, lift_option_type_def, return_def, raise_def,
       AllCaseEqs(), LET_THM, option_CASE_rator] >>
  strip_tac >> gvs[] >>
  rename1 `eval_expr cx e st = (INL tvl, st1)` >>
  rename1 `materialise cx tvl st1 = (INL v, st2)` >>
  rename1 `new_variable id tv v st2 = (INL u, st')` >>
  drule_all eval_expr_type_preservation >> strip_tac >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  drule_at(Pat`materialise`) materialise_preserves_type >>
  `env.type_defs = get_tenv cx` by gvs[env_consistent_def] >>
  gvs[expr_runtime_typed_def] >>
  disch_then drule_all >> strip_tac >>
  drule_at(Pat`new_variable`) extend_local_env_consistent_after_new_variable >>
  simp[extend_local_def] >>
  disch_then (drule_at Any)
  >- (
    disch_then irule >> simp[] >>
    drule materialise_state >>
    rw[] >>
    drule_all eval_expr_preserves_ec >> simp[]) >>
  strip_tac >>
  irule new_variable_preserves_state_well_typed >>
  goal_assum(drule_at(Pat`new_variable`)) >>
  simp[] >> goal_assum drule
QED

Theorem non_decl_stmt_env_consistent_after_success:
  type_stmt env ret_ty s = SOME env /\ env_consistent env cx st /\ state_well_typed st /\
  eval_stmt cx s st = (INL u, st') ==>
  env_consistent env cx st' /\ state_well_typed st'
Proof
  cheat
QED

Theorem eval_stmt_success_accounts_well_typed:
  accounts_well_typed st.accounts /\ eval_stmt cx s st = (INL u, st') ==>
  accounts_well_typed st'.accounts
Proof
  cheat
QED

Theorem eval_stmt_exception_accounts_well_typed:
  accounts_well_typed st.accounts /\ eval_stmt cx s st = (INR exn, st') ==>
  accounts_well_typed st'.accounts
Proof
  cheat
QED

(* ===== Statement soundness ===== *)

Theorem eval_stmt_no_type_error:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmt cx s st)
Proof
  cheat
QED

Theorem eval_stmt_type_preservation_success:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  rpt gen_tac >> strip_tac >> Cases_on `s` >>
  TRY(rename1 `eval_stmt cx (AnnAssign id typ e) st = _` >> suspend "AnnAssign") >>
  gvs[type_stmt_def] >>
  TRY(rename1 `eval_stmt cx Pass st = _` >> suspend "Pass") >>
  TRY(rename1 `eval_stmt cx Continue st = _` >> suspend "Continue") >>
  TRY(rename1 `eval_stmt cx Break st = _` >> suspend "Break") >>
  TRY(rename1 `eval_stmt cx (Return o') st = _` >> suspend "Return") >>
  TRY(rename1 `eval_stmt cx (Raise r) st = _` >> suspend "Raise") >>
  TRY(rename1 `eval_stmt cx (Assert e a) st = _` >> suspend "Assert") >>
  TRY(rename1 `eval_stmt cx (Log id es) st = _` >> suspend "Log") >>
  TRY(rename1 `eval_stmt cx (Append bt e) st = _` >> suspend "Append") >>
  TRY(rename1 `eval_stmt cx (Assign tgt e) st = _` >> suspend "Assign") >>
  TRY(rename1 `eval_stmt cx (AugAssign ty bt bop e) st = _` >> suspend "AugAssign") >>
  TRY(rename1 `eval_stmt cx (If e ss1 ss2) st = _` >> suspend "If") >>
  TRY(rename1 `eval_stmt cx (For id typ it n body) st = _` >> suspend "For") >>
  TRY(rename1 `eval_stmt cx (Expr e) st = _` >> suspend "Expr")
QED

Resume eval_stmt_type_preservation_success[Pass]:
  gvs[Once evaluate_def, return_def]
QED

Resume eval_stmt_type_preservation_success[Continue]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_stmt_type_preservation_success[Break]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_stmt_type_preservation_success[Return]:
  Cases_on `o'` >> gvs[type_stmt_def, Once evaluate_def, bind_def, raise_def, AllCaseEqs()]
QED

Resume eval_stmt_type_preservation_success[Raise]:
  Cases_on `r` >> gvs[type_stmt_def, Once evaluate_def, bind_def, raise_def, AllCaseEqs()]
QED

Resume eval_stmt_type_preservation_success[Assert]:
  `env' = env` by (Cases_on `a` >> gvs[type_stmt_def]) >> gvs[] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[Log]:
  `type_stmt env ret_ty (Log id es) = SOME env` by simp[type_stmt_def] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[AnnAssign]:
  drule_all AnnAssign_env_consistent_after_new_variable >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >>
  rw[]
QED

Resume eval_stmt_type_preservation_success[Append]:
  `env' = env` by gvs[type_stmt_def, AllCaseEqs()] >> gvs[] >>
  `type_stmt env ret_ty (Append bt e) = SOME env` by gvs[type_stmt_def, AllCaseEqs()] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[Assign]:
  `type_stmt env ret_ty (Assign tgt e) = SOME env` by simp[type_stmt_def] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[AugAssign]:
  `type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env` by simp[type_stmt_def] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[If]:
  `type_stmt env ret_ty (If e ss1 ss2) = SOME env` by simp[type_stmt_def] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[For]:
  `type_stmt env ret_ty (For id typ it n body) = SOME env` by simp[type_stmt_def] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Resume eval_stmt_type_preservation_success[Expr]:
  `type_stmt env ret_ty (Expr e) = SOME env` by simp[type_stmt_def] >>
  drule_all non_decl_stmt_env_consistent_after_success >> strip_tac >>
  drule_all eval_stmt_success_accounts_well_typed >> rw[]
QED

Finalise eval_stmt_type_preservation_success

Theorem eval_stmt_type_preservation_exception:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn) /\ accounts_well_typed st'.accounts
Proof
  cheat
QED

Theorem eval_stmt_type_preservation_exception_state:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st'
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem eval_stmt_type_preservation_exception_ok:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem stmt_error_ok_type_defs_eq:
  env1.type_defs = env2.type_defs ==>
  (stmt_error_ok env1 ret_ty r <=> stmt_error_ok env2 ret_ty r)
Proof
  Cases_on `r` >> simp[stmt_error_ok_def, return_exception_typed_def] >>
  Cases_on `y` >> simp[value_runtime_typed_def]
QED

Theorem type_stmt_preserves_stmt_error_ok:
  type_stmt env ret_ty s = SOME env1 /\ stmt_error_ok env1 ret_ty r ==>
  stmt_error_ok env ret_ty r
Proof
  strip_tac >>
  drule type_stmt_env_preserved_static >> strip_tac >>
  fs[stmt_error_ok_def, return_exception_typed_def, value_runtime_typed_def]
QED

Theorem eval_stmt_type_preservation_exception_state_pair:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem eval_stmts_no_type_error:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st`, `env`, `ss`] >>
  Induct >>
  rw[Once evaluate_def, no_type_error_eval_def, no_type_error_result_def, return_def] >>
  (* cons case *)
  gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_stmt cx h st` >> gvs[no_type_error_eval_def, no_type_error_result_def] >>
  Cases_on `q` >> gvs[no_type_error_eval_def, no_type_error_result_def]
  >- (
    drule_all eval_stmt_type_preservation_success >> strip_tac >>
    first_x_assum drule_all >> rw[no_type_error_eval_def, no_type_error_result_def]) >>
  drule_all eval_stmt_no_type_error >>
  gvs[no_type_error_eval_def, no_type_error_result_def]
QED

Theorem eval_stmts_type_preservation_success:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st'`, `u`, `st`, `env`, `ss`] >>
  Induct
  >- simp[Once evaluate_def, return_def, type_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  (* cons case *)
  gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_stmt cx h st` >> gvs[] >>
  drule_all eval_stmt_type_preservation_success >> strip_tac >>
  first_x_assum drule_all >> rw[]
QED

Theorem eval_stmts_type_preservation_exception:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st'`, `exn`, `st`, `env`, `ss`] >>
  Induct >> simp[Once evaluate_def, return_def] >>
  simp[type_stmt_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  reverse(gvs[bind_def, ignore_bind_def, AllCaseEqs()]) >- (
    drule_all eval_stmt_type_preservation_exception >> rw[] ) >>
  drule_all eval_stmt_type_preservation_success >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >>
  drule_all type_stmt_preserves_stmt_error_ok >>
  rw[]
QED

(* ===== Loop preservation ===== *)

Theorem eval_for_preserves_state_well_typed:
  state_well_typed st /\ env_consistent env cx st /\
  evaluate_type env.type_defs ty = SOME tv /\ EVERY (value_has_type tv) vs /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_for cx tv id body vs st = (INL u, st') ==>
  state_well_typed st'
Proof
  MAP_EVERY qid_spec_tac [`st'`, `u`, `st`, `vs`] >>
  Induct >>
  simp[Once evaluate_def, return_def] >>
  simp[Once evaluate_def, bind_def, push_scope_with_var_def, return_def,
       finally_def, try_def, ignore_bind_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx body st_push` >>
  (* Case split on eval_stmts result *)
  Cases_on `eval_stmts cx body st_push` >>
  gvs[bind_def] >>
  rename1 `eval_stmts cx body st_push = (body_res, st_body)` >>
  (* Establish st_push is well-typed *)
  `well_formed_type_value tv` by
    (gvs[env_consistent_def] >> irule evaluate_type_well_formed_type_value >> metis_tac[]) >>
  `state_well_typed st_push` by
    (gvs[Abbr`st_push`, state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]) >>
  (* Establish env_consistent for extended env *)
  `env_consistent (extend_local env id ty F) cx st_push` by
    (simp[Abbr`st_push`] >> irule push_scope_with_var_env_consistent >>
     gvs[env_consistent_def] >> cheat) >>
  (* Use eval_stmts preservation (cheated) to get st_body well-typed *)
  `state_well_typed st_body` by
    (Cases_on `body_res` >> gvs[] >> cheat) >>
  cheat
QED

(* ===== Top-level theorem shape ===== *)

Theorem function_body_type_sound:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  type_stmts env ret_ty body = SOME env_after ==>
  no_type_error_eval (eval_stmts cx body st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED

