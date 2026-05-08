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
  wordsLib markerLib

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

(* TOP-LEVEL WORKHORSE: mutual no-TypeError proof for statements, statement
 * lists, and for-loops.  This follows the evaluator recursion and is the
 * intended final shape for removing the no-TypeError cheats. *)
Theorem eval_all_no_type_error_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    no_type_error_result res) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    no_type_error_result res) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_iterator cx it st = (res, st') ==>
    no_type_error_result res) /\
  (!cx tgt. !env ty st res st'.
    well_typed_atarget env tgt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_target cx tgt st = (res, st') ==>
    no_type_error_result res) /\
  (!cx tgts. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_targets cx tgts st = (res, st') ==>
    no_type_error_result res) /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    no_type_error_result res) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_for cx tyv id body vs st = (res, st') ==>
    no_type_error_result res) /\
  (!cx e. !env st res st'.
    well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx e st = (res, st') ==>
    no_type_error_result res) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    no_type_error_result res)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  TRY(rename1 `Pass` >> suspend "Pass") >>
  TRY(rename1 `Continue` >> suspend "Continue") >>
  TRY(rename1 `Break` >> suspend "Break") >>
  TRY(rename1 `Return NONE` >> suspend "Return_NONE") >>
  TRY(rename1 `Return (SOME _)` >> suspend "Return_SOME") >>
  TRY(rename1 `Raise RaiseBare` >> suspend "RaiseBare") >>
  TRY(rename1 `Raise RaiseUnreachable` >> suspend "RaiseUnreachable") >>
  TRY(rename1 `Raise (RaiseReason _)` >> suspend "RaiseReason") >>
  TRY(rename1 `AssertBare` >> suspend "AssertBare") >>
  TRY(rename1 `AssertUnreachable` >> suspend "AssertUnreachable") >>
  TRY(rename1 `AssertReason` >> suspend "AssertReason") >>
  TRY(rename1 `Log` >> suspend "Log") >>
  TRY(rename1 `AnnAssign` >> suspend "AnnAssign") >>
  TRY(rename1 `Append` >> suspend "Append") >>
  TRY(rename1 `Assign` >> suspend "Assign") >>
  TRY(rename1 `AugAssign` >> suspend "AugAssign") >>
  TRY(rename1 `If` >> suspend "If") >>
  TRY(rename1 `For` >> suspend "For") >>
  TRY(rename1 `Expr` >> suspend "Expr") >>
  TRY(rename1 `eval_stmts _ []` >> suspend "Stmts_nil") >>
  TRY(rename1 `eval_stmts _ (_::_)` >> suspend "Stmts_cons") >>
  TRY(rename1 `eval_for _ _ _ _ []` >> suspend "For_nil") >>
  TRY(rename1 `eval_for _ _ _ _ (_::_)` >> suspend "For_cons") >>
  TRY(rename1 `Array` >> suspend "Iterator_Array") >>
  TRY(rename1 `Range` >> suspend "Iterator_Range") >>
  TRY(rename1 `BaseTarget` >> suspend "Target_Base") >>
  TRY(rename1 `TupleTarget` >> suspend "Target_Tuple") >>
  TRY(rename1 `eval_targets _ []` >> suspend "Targets_nil") >>
  TRY(rename1 `eval_targets _ (_::_)` >> suspend "Targets_cons") >>
  TRY(rename1 `NameTarget` >> suspend "BaseTarget_Name") >>
  TRY(rename1 `BareGlobalNameTarget` >> suspend "BaseTarget_BareGlobal") >>
  TRY(rename1 `TopLevelNameTarget` >> suspend "BaseTarget_TopLevel") >>
  TRY(rename1 `SubscriptTarget` >> suspend "BaseTarget_Subscript") >>
  TRY(rename1 `AttributeTarget` >> suspend "BaseTarget_Attribute") >>
  TRY(rename1 `Name` >> suspend "Expr_Name") >>
  TRY(rename1 `BareGlobalName` >> suspend "Expr_BareGlobalName") >>
  TRY(rename1 `TopLevelName` >> suspend "Expr_TopLevelName") >>
  TRY(rename1 `FlagMember` >> suspend "Expr_FlagMember") >>
  TRY(rename1 `IfExp` >> suspend "Expr_IfExp") >>
  TRY(rename1 `Literal` >> suspend "Expr_Literal") >>
  TRY(rename1 `StructLit` >> suspend "Expr_StructLit") >>
  TRY(rename1 `Subscript` >> suspend "Expr_Subscript") >>
  TRY(rename1 `Attribute` >> suspend "Expr_Attribute") >>
  TRY(rename1 `Builtin` >> suspend "Expr_Builtin") >>
  TRY(rename1 `TypeBuiltin` >> suspend "Expr_TypeBuiltin") >>
  TRY(rename1 `Pop` >> suspend "Expr_Pop") >>
  TRY(rename1 `IntCall` >> suspend "Expr_Call_IntCall") >>
  TRY(rename1 `ExtCall` >> suspend "Expr_Call_ExtCall") >>
  TRY(rename1 `Send` >> suspend "Expr_Call_Send") >>
  TRY(rename1 `RawCallTarget` >> suspend "Expr_Call_RawCallTarget") >>
  TRY(rename1 `RawLog` >> suspend "Expr_Call_RawLog") >>
  TRY(rename1 `RawRevert` >> suspend "Expr_Call_RawRevert") >>
  TRY(rename1 `SelfDestructTarget` >> suspend "Expr_Call_SelfDestructTarget") >>
  TRY(rename1 `CreateTarget` >> suspend "Expr_Call_CreateTarget") >>
  TRY(rename1 `eval_exprs _ []` >> suspend "Exprs_nil") >>
  TRY(rename1 `eval_exprs _ (_::_)` >> suspend "Exprs_cons")
QED

Resume eval_all_no_type_error_mutual[Pass]:
  gvs[Once evaluate_def, return_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[Continue]:
  gvs[Once evaluate_def, raise_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[Break]:
  gvs[Once evaluate_def, raise_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[Stmts_nil]:
  gvs[Once evaluate_def, return_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[Return_NONE]:
  gvs[type_stmt_def, Once evaluate_def, raise_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, Once evaluate_def, bind_def, raise_def, AllCaseEqs(),
      no_type_error_result_def] >>
  first_x_assum drule_all >> rw[no_type_error_result_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[no_type_error_result_def]) >>
  drule_all eval_expr_type_preservation >> strip_tac >>
  gvs[expr_runtime_typed_def] >>
  drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
  drule_all materialise_typed_non_none_no_type_error >> simp[]
QED

Resume eval_all_no_type_error_mutual[RaiseBare]:
  gvs[type_stmt_def, Once evaluate_def, raise_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[RaiseUnreachable]:
  gvs[type_stmt_def, Once evaluate_def, raise_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[RaiseReason]:
  cheat
QED

Resume eval_all_no_type_error_mutual[AssertBare]:
  cheat
QED

Resume eval_all_no_type_error_mutual[AssertUnreachable]:
  cheat
QED

Resume eval_all_no_type_error_mutual[AssertReason]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Log]:
  cheat
QED

Resume eval_all_no_type_error_mutual[AnnAssign]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Append]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Assign]:
  cheat
QED

Resume eval_all_no_type_error_mutual[AugAssign]:
  cheat
QED

Resume eval_all_no_type_error_mutual[If]:
  cheat
QED

Resume eval_all_no_type_error_mutual[For]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Stmts_cons]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Iterator_Array]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Iterator_Range]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Target_Base]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Target_Tuple]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Targets_nil]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Targets_cons]:
  cheat
QED

Resume eval_all_no_type_error_mutual[BaseTarget_Name]:
  cheat
QED

Resume eval_all_no_type_error_mutual[BaseTarget_BareGlobal]:
  cheat
QED

Resume eval_all_no_type_error_mutual[BaseTarget_TopLevel]:
  cheat
QED

Resume eval_all_no_type_error_mutual[BaseTarget_Subscript]:
  cheat
QED

Resume eval_all_no_type_error_mutual[BaseTarget_Attribute]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Name]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_BareGlobalName]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_TopLevelName]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_FlagMember]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_IfExp]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Literal]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_StructLit]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Subscript]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Attribute]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Builtin]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_TypeBuiltin]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Pop]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_IntCall]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_ExtCall]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_Send]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_RawCallTarget]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_RawLog]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_RawRevert]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_SelfDestructTarget]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Expr_Call_CreateTarget]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Exprs_nil]:
  cheat
QED

Resume eval_all_no_type_error_mutual[Exprs_cons]:
  cheat
QED

Resume eval_all_no_type_error_mutual[For_nil]:
  gvs[Once evaluate_def, return_def, no_type_error_result_def]
QED

Resume eval_all_no_type_error_mutual[For_cons]:
  cheat
QED

Finalise eval_all_no_type_error_mutual

Theorem eval_stmt_stmts_for_no_type_error_mutual:
  (!cx s st res st' env ret_ty env'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    no_type_error_result res) /\
  (!cx ss st res st' env ret_ty env'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    no_type_error_result res) /\
  (!cx tyv id body vs st res st' env ret_ty ty env_after.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_for cx tyv id body vs st = (res, st') ==>
    no_type_error_result res)
Proof
  metis_tac[eval_all_no_type_error_mutual]
QED

Theorem eval_stmt_no_type_error:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmt cx s st)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx s st` >>
  simp[no_type_error_eval_def] >>
  irule (cj 1 eval_stmt_stmts_for_no_type_error_mutual) >>
  metis_tac[]
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

