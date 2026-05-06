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
  state_well_typed st' /\ env_consistent env' cx st'
Proof
  cheat
QED

Theorem eval_stmt_type_preservation_exception:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  cheat
QED

Theorem eval_stmts_no_type_error:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  cheat
QED

Theorem eval_stmts_type_preservation_success:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st'
Proof
  cheat
QED

Theorem eval_stmts_type_preservation_exception:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  cheat
QED

(* ===== Loop preservation ===== *)

Theorem eval_for_preserves_state_well_typed:
  state_well_typed st /\ env_consistent env cx st /\
  evaluate_type env.type_defs ty = SOME tv /\ EVERY (value_has_type tv) vs /\
  type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_for cx tv id body vs st = (INL u, st') ==>
  state_well_typed st'
Proof
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

