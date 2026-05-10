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
  vyperTypeAssignSoundness vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
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

Theorem no_control_exc_return_exception_typed:
  no_control_exc exn ==> return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> rw[no_control_exc_def, return_exception_typed_def]
QED

Theorem expr_runtime_typed_hashmap_ref_place:
  expr_runtime_typed env e tv /\ is_HashMapRef tv ==>
  ?kt vt. type_place_expr env e = SOME (HashMapT kt vt)
Proof
  cheat
QED

Theorem eval_expr_exception_return_typed:
  eval_expr cx e st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 1 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_exprs_exception_return_typed:
  eval_exprs cx es st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 2 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_target_no_control:
  (!cx tgt st exn st'.
    eval_target cx tgt st = (INR exn, st') ==> no_control_exc exn) /\
  (!cx tgts st exn st'.
    eval_targets cx tgts st = (INR exn, st') ==> no_control_exc exn) /\
  (!cx bt st exn st'.
    eval_base_target cx bt st = (INR exn, st') ==> no_control_exc exn)
Proof
  cheat
QED

Theorem value_runtime_typed_env_static:
  env'.type_defs = env.type_defs /\ value_runtime_typed env' ty v ==>
  value_runtime_typed env ty v
Proof
  rw[value_runtime_typed_def] >> metis_tac[]
QED

Theorem return_exception_typed_env_static:
  env'.type_defs = env.type_defs /\ return_exception_typed env' ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> rw[return_exception_typed_def] >>
  metis_tac[value_runtime_typed_env_static]
QED

Theorem materialise_preserves_value_type:
  state_well_typed st /\ toplevel_value_typed tvl tv /\ well_formed_type_value tv /\
  materialise cx tvl st = (INL v, st') ==>
  value_has_type tv v
Proof
  metis_tac[materialise_preserves_type]
QED


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

Definition env_extends_def:
  env_extends env env' <=>
    env'.type_defs = env.type_defs /\ env'.current_src = env.current_src /\
    env'.fn_sigs = env.fn_sigs /\ env'.bare_globals = env.bare_globals /\
    env'.toplevel_vtypes = env.toplevel_vtypes /\ env'.flag_members = env.flag_members /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP env'.var_types id = SOME ty) /\
    (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP env'.var_assignable id = SOME T)
End

Theorem env_extends_refl[simp]:
  env_extends env env
Proof
  simp[env_extends_def]
QED

Theorem env_extends_trans:
  env_extends env1 env2 /\ env_extends env2 env3 ==> env_extends env1 env3
Proof
  rw[env_extends_def] >> metis_tac[]
QED

Theorem type_stmt_var_assignable_T_preserve:
  env_maps_wf env /\ type_stmt env ret_ty s = SOME env' /\
  FLOOKUP env.var_assignable id = SOME T ==>
  FLOOKUP env'.var_assignable id = SOME T
Proof
  Cases_on `s` >> gvs[type_stmt_def, AllCaseEqs(), extend_local_def, FLOOKUP_UPDATE] >>
  TRY (rename1 `Assert e a` >> Cases_on `a` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Raise r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  TRY (rename1 `Return r` >> Cases_on `r` >> gvs[type_stmt_def]) >>
  rw[] >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `string_to_num s'' = id` >> gvs[] >>
  fs[env_maps_wf_def, TO_FLOOKUP]
QED

Theorem type_stmts_var_assignable_T_preserve:
  env_maps_wf env /\ type_stmts env ret_ty ss = SOME env' /\
  FLOOKUP env.var_assignable id = SOME T ==>
  FLOOKUP env'.var_assignable id = SOME T
Proof
  MAP_EVERY qid_spec_tac [`env`, `env'`] >>
  Induct_on `ss` >> gvs[type_stmt_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP env''.var_assignable id = SOME T` by
    metis_tac[type_stmt_var_assignable_T_preserve] >>
  `env_maps_wf env''` by metis_tac[type_stmt_env_maps_wf] >>
  first_x_assum drule_all >> simp[]
QED

Theorem type_stmt_env_extends:
  env_maps_wf env /\ type_stmt env ret_ty s = SOME env' ==> env_extends env env'
Proof
  strip_tac >>
  drule_all type_stmt_env_preserved_static >> strip_tac >>
  rw[env_extends_def] >>
  metis_tac[type_stmt_var_types_preserve, type_stmt_var_assignable_T_preserve]
QED

Theorem type_stmts_env_extends:
  env_maps_wf env /\ type_stmts env ret_ty ss = SOME env' ==> env_extends env env'
Proof
  strip_tac >>
  drule_all type_stmts_env_preserved_static >> strip_tac >>
  rw[env_extends_def] >>
  metis_tac[type_stmts_var_types_preserve, type_stmts_var_assignable_T_preserve]
QED

Theorem env_extends_return_exception_typed:
  env_extends env env' /\ return_exception_typed env' ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  Cases_on `exn` >> gvs[return_exception_typed_def] >>
  metis_tac[value_runtime_typed_env_static, env_extends_def]
QED

Theorem env_extends_env_consistent_after_pop:
  env_maps_wf env /\ env_consistent env cx st_outer /\
  preserves_tv cx st_outer (st_body with scopes := tl) /\
  env_extends env env_body /\ env_consistent env_body cx st_body /\
  st_body.scopes = h::tl /\ tl <> [] /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE) /\
  (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP h id = NONE) /\
  (!id ty.
     FLOOKUP env_body.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id tl = NONE) ==>
  env_consistent env cx (st_body with scopes := tl)
Proof
  strip_tac >>
  fs[env_consistent_def] >>
  fs[env_extends_def] >>
  simp[env_consistent_def] >>
  conj_tac >- (
    qpat_x_assum `env_scopes_consistent env_body cx st_body` mp_tac >>
    simp[env_scopes_consistent_def] >> strip_tac >>
    rw[env_scopes_consistent_def]
    >- (qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> _` drule >> strip_tac >>
        qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP env_body.var_types id = SOME ty` drule >>
        strip_tac >>
        qpat_x_assum `!id ty. FLOOKUP env_body.var_types id = SOME ty ==> _` drule >>
        simp[lookup_scopes_def] >>
        Cases_on `FLOOKUP h id` >> gvs[])
    >- (Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
        qpat_x_assum `!id' entry'. lookup_scopes id' (h::tl) = SOME entry' ==> _`
          (qspec_then `id` mp_tac) >>
        simp[lookup_scopes_def] >>
        Cases_on `FLOOKUP h id` >> gvs[] >>
        Cases_on `FLOOKUP env_body.var_types id` >> gvs[] >>
        rename1 `FLOOKUP env_body.var_types id = SOME ty` >>
        first_x_assum drule_all >> simp[])
    >- (qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP env_body.var_types id = SOME ty` drule >>
        strip_tac >>
        qpat_x_assum `!id' ty' entry'. FLOOKUP env_body.var_types id' = SOME ty' /\ _ ==> _`
          (qspecl_then [`id`, `ty`, `entry`] mp_tac) >>
        simp[lookup_scopes_def] >>
        Cases_on `FLOOKUP h id` >> gvs[])
    >- (fs[env_scopes_consistent_def] >> metis_tac[]) >>
    qpat_x_assum `!id. FLOOKUP env.var_assignable id = SOME T ==> _` drule >> strip_tac >>
    qpat_x_assum `!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP env_body.var_assignable id = SOME T` drule >>
    strip_tac >>
    qpat_x_assum `!id'. FLOOKUP env_body.var_assignable id' = SOME T ==> _` drule >>
    simp[lookup_scopes_def] >>
    Cases_on `FLOOKUP h id` >> gvs[] >>
    metis_tac[]) >>
  qpat_x_assum `env_immutables_consistent env_body cx st_body` mp_tac >>
  simp[env_immutables_consistent_def] >> strip_tac >>
  rw[env_immutables_consistent_def]
  >- (qpat_x_assum `preserves_tv _ _ _` mp_tac >> simp[preserves_tv_def] >> metis_tac[])
  >- (qpat_x_assum `preserves_tv _ _ _` mp_tac >> simp[preserves_tv_def] >> metis_tac[]) >>
  qpat_x_assum `!src id ty ts. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ _ ==> _`
    (qspecl_then [`src`, `id`, `ty`, `ts`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem type_stmts_env_consistent_after_pop:
  env_maps_wf env /\ env_consistent env cx st_outer /\
  preserves_tv cx st_outer (st_body with scopes := tl) /\
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env' cx st_body /\
  st_body.scopes = h::tl /\ tl <> [] /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> FLOOKUP h id = NONE) /\
  (!id. FLOOKUP env.var_assignable id = SOME T ==> FLOOKUP h id = NONE) /\
  (!id ty.
     FLOOKUP env'.var_types id = SOME ty /\ FLOOKUP env.var_types id = NONE ==>
     lookup_scopes id tl = NONE) ==>
  env_consistent env cx (st_body with scopes := tl)
Proof
  strip_tac >>
  `env_extends env env'` by metis_tac[type_stmts_env_extends] >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (qexists_tac `env'` >> simp[]) >>
  qexists_tac `st_outer` >> simp[]
QED

Theorem eval_stmts_pushed_scope_env_consistent_after_pop:
  env_maps_wf env /\ env_consistent env cx st /\
  preserves_tv cx (st with scopes updated_by CONS FEMPTY) st_body /\
  eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (res, st_body) /\
  env_extends env env_body /\ env_consistent env_body cx st_body ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  `st with scopes updated_by CONS FEMPTY =
   st with scopes := FEMPTY::st.scopes`
  by simp[evaluation_state_component_equality] >>
  Cases_on `st_body.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (
    drule eval_stmts_preserves_scopes_len >> simp[] >>
    strip_tac >>
    `st.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
    Cases_on `st.scopes` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  conj_tac >- (
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      `FLOOKUP (HD st_body.scopes) id = NONE` suffices_by simp[] >>
      irule lookup_scopes_not_in_new_head >> simp[] >>
      qexists_tac `cx` >> qexists_tac `entry` >> qexists_tac `res` >>
      qexists_tac `st.scopes` >> qexists_tac `st` >> simp[] >>
      qexists_tac `FEMPTY` >> qexists_tac `ss` >> simp[]) >>
    rpt strip_tac >> fs[] >>
    `?entry. lookup_scopes id st.scopes = SOME entry` by (
      qpat_x_assum`env_consistent _ _ st`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    `FLOOKUP h id = NONE` suffices_by simp[] >>
    `FLOOKUP (HD st_body.scopes) id = NONE` suffices_by simp[] >>
    irule lookup_scopes_not_in_new_head >> simp[] >>
    qexists_tac `cx` >> qexists_tac `entry` >> qexists_tac `res` >>
    qexists_tac `st.scopes` >> qexists_tac `st` >> simp[] >>
    qexists_tac `FEMPTY` >> qexists_tac `ss` >> simp[]) >>
  conj_tac >- (
    qexists_tac `env_body` >> simp[] >>
    rpt strip_tac >> fs[] >>
    `lookup_scopes id st.scopes = NONE` by (
      qpat_x_assum`env_consistent env cx st`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
      Cases_on `lookup_scopes id st.scopes` >> gvs[] >>
      metis_tac[optionTheory.IS_SOME_DEF]) >>
    qspecl_then [`cx`, `ss`, `st`, `FEMPTY`, `st.scopes`, `res`, `st_body`, `id`, `h`, `t`]
      mp_tac eval_stmts_preserves_tail_lookup_none >>
    simp[]) >>
  qexists_tac `st` >> simp[] >>
  qspecl_then [`cx`, `ss`, `FEMPTY`, `st`, `res`, `st_body`]
    mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
  simp[]
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
  `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
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

Theorem eval_base_target_target_runtime_typed:
  well_typed_target env bt ty /\ env_consistent env cx st /\ state_well_typed st /\
  eval_base_target cx bt st = (INL (loc,sbs), st') ==>
  target_runtime_typed env cx st' (BaseTarget bt) ty (BaseTargetV loc sbs)
Proof
  cheat
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

(* ===== Scope-bracket helpers for block statements ===== *)

Theorem scope_bracket_decompose:
  (!q st_body. body (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body pop_scope od) st = (res, st') ==>
  ?q st_body.
    body (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
    st' = st_body with scopes := TL st_body.scopes /\
    (((?x. q = INL x) ==> ?u. res = INL u) /\
     (!e. q = INR e ==> res = INR e))
Proof
  rpt strip_tac >>
  gvs[push_scope_def, finally_def, pop_scope_def,
      return_def, raise_def, bind_def, ignore_bind_def,
      AllCaseEqs()] >>
  Cases_on `body (st with scopes updated_by CONS FEMPTY)` >>
  Cases_on `q` >>
  gvs[AllCaseEqs(), pop_scope_def, return_def, raise_def] >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `r.scopes` >> gvs[return_def, raise_def,
    evaluation_state_component_equality]
QED

Theorem scope_bracket_preserves_swt:
  eval_stmts cx ss (st with scopes updated_by CONS sc) = (res, st_body) /\
  state_well_typed st_body ==>
  state_well_typed (st_body with scopes := TL st_body.scopes)
Proof
  rpt strip_tac >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `st_body.scopes` >> gvs[] >>
  irule pop_scope_preserves_state_well_typed >>
  qexists_tac `st_body` >>
  qexists_tac `()` >>
  simp[pop_scope_def, return_def]
QED

Theorem scope_bracket_preserves:
  env_maps_wf env /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
  state_well_typed st_body /\
  env_consistent env_after cx st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts
Proof
  strip_tac
  >> conj_tac >- (drule scope_bracket_preserves_swt >> simp[])
  >> conj_tac >- (irule scope_bracket_preserves_ec >>
      conj_tac >- rw[] >>
      goal_assum(drule_at(Pat`type_stmts`)) >>
      goal_assum(drule_at(Pat`eval_stmts`)) >>
      simp[])
  >> simp[evaluation_state_component_equality]
QED

Theorem scope_bracket_result_post:
  (!e. q = INR e ==> res = INR e) /\
  ((?x. q = INL x) ==> res = INL ()) /\
  no_type_error_result q /\
  (case q of INR exn => return_exception_typed env ret_ty exn | _ => T) ==>
  no_type_error_result res /\
  (case res of INR exn => return_exception_typed env ret_ty exn | _ => T)
Proof
  CASE_TAC >> strip_tac >> gvs[no_type_error_result_def]
QED

Theorem scope_bracket_post:
  env_maps_wf env /\
  env_consistent env cx st /\
  (!q st_body. body (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body pop_scope od) st = (res, st_final) /\
  (!q st_body.
     body (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==>
     state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
     no_type_error_result q /\
     case q of
     | INL _ => env_consistent env cx (st_body with scopes := TL st_body.scopes)
     | INR exn => env_consistent env cx (st_body with scopes := TL st_body.scopes) /\ return_exception_typed env ret_ty exn) ==>
  state_well_typed st_final /\ accounts_well_typed st_final.accounts /\ no_type_error_result res /\
  case res of
  | INL _ => env_consistent env cx st_final
  | INR exn => env_consistent env cx st_final /\ return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `do push_scope; finally body pop_scope od st = (res,st_final)` mp_tac >>
  qpat_x_assum `!q st_body. body _ = _ ==> st_body.scopes <> []` mp_tac >>
  strip_tac >> strip_tac >>
  `?q st_body.
     body (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
     st_final = st_body with scopes := TL st_body.scopes /\
     (((?x. q = INL x) ==> ?u. res = INL u) /\
      (!e. q = INR e ==> res = INR e))` by
    (irule scope_bracket_decompose >> simp[]) >>
  gvs[] >>
  qmatch_assum_rename_tac`no_type_error_result r1` >>
  Cases_on `st_body.scopes` >> gvs[] >>
  `state_well_typed (st_body with scopes := t)` by (
    drule pop_scope_preserves_state_well_typed >>
    simp[pop_scope_def, return_def, raise_def]) >>
  Cases_on`r1` >> gvs[no_type_error_result_def]
QED

Theorem eval_all_type_sound_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => ?env_exn. env_extends env env_exn /\ env_consistent env_exn cx st' /\
                           return_exception_typed env_exn ret_ty exn) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs
    | INR _ => T) /\
  (!cx tgt. !env ty st res st'.
    well_typed_atarget env tgt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_target cx tgt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL gv => target_runtime_typed env cx st' tgt ty gv
    | INR _ => T) /\
  (!cx tgts. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_targets cx tgts st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL gvs => LIST_REL3 (\t ty gv. target_runtime_typed env cx st' t ty gv) tgts tys gvs
    | INR _ => T) /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL (loc,sbs) => base_target_value_shape env bt loc sbs
    | INR _ => T) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_for cx tyv id body vs st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
    no_type_error_result res /\
    case res of
    | INR exn => return_exception_typed env ret_ty exn
    | INL _ => T) /\
  (!cx e. !env st res st'.
    well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx e st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_runtime_typed env e tv
    | INR _ => T) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => exprs_runtime_typed env es vs
    | INR _ => T)
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

Resume eval_all_type_sound_mutual[Pass]:
  gvs[evaluate_def, return_def, no_type_error_result_def, type_stmt_def]
QED

Resume eval_all_type_sound_mutual[Continue]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[Break]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def, value_runtime_typed_def, value_has_type_def,
      evaluate_type_def]
QED

Resume eval_all_type_sound_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `er` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tv,s1)` >>
    Cases_on `materialise cx tv s1` >>
    rename1 `materialise cx tv s1 = (mr,s2)` >>
    Cases_on `mr` >> gvs[raise_def, no_type_error_result_def]
    >- (
      drule materialise_state >> strip_tac >> gvs[] >>
      strip_tac >> gvs[] >>
      gvs[expr_runtime_typed_def, return_exception_typed_def,
          value_runtime_typed_def] >>
      irule materialise_preserves_value_type >>
      simp[] >>
      metis_tac[evaluate_type_well_formed_type_value]) >>
    drule materialise_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    conj_tac >- (
      gvs[expr_runtime_typed_def] >>
      drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
      drule_all materialise_typed_non_none_no_type_error >> simp[]) >>
    drule materialise_no_control >> strip_tac >>
    Cases_on `y` >> gvs[no_control_exc_def, return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[RaiseReason]:
  cheat
QED

Resume eval_all_type_sound_mutual[AssertBare]:
  cheat
QED

Resume eval_all_type_sound_mutual[AssertUnreachable]:
  cheat
QED

Resume eval_all_type_sound_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum`eval_stmt`mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  qhdtm_x_assum`type_stmt`mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> reverse strip_tac >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> simp[] >>
    drule_all eval_expr_exception_return_typed >>
    rw[] >> gvs[no_type_error_result_def]
  ) >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  first_x_assum (funpow 3 drule_then drule) >> simp[] >> strip_tac >>
  qhdtm_x_assum`expr_runtime_typed`mp_tac >>
  asm_rewrite_tac[expr_runtime_typed_def] >>
  simp[evaluate_type_def] >> strip_tac >>
  qho_match_abbrev_tac`P res st'` >>
  drule_then (drule_then irule) switch_BoolV_post >>
  conj_tac >- (rw[return_def,Abbr`P`] >> rw[no_type_error_result_def]) >>
  qhdtm_x_assum`switch_BoolV`kall_tac >>
  simp[bind_def,AllCaseEqs(),PULL_EXISTS,raise_def] >>
  rpt gen_tac >>
  strip_tac >> gvs[Abbr`P`] >>
  imp_res_tac get_Value_state >>
  imp_res_tac lift_option_type_state >>
  gvs[expr_runtime_typed_def,evaluate_type_def] >>
  TRY(
    gvs[no_type_error_result_def,return_exception_typed_def] >>
    NO_TAC ) >>
  TRY(Cases_on`stv` >> gvs[toplevel_value_typed_def, return_def] >>
      TRY (
      Cases_on`sv` >>
      gvs[value_has_type_def,dest_StringV_def,
          lift_option_type_def]))
   >> gvs[no_type_error_result_def]
   >> drule eval_expr_exception_return_typed
   >> rw[]
QED

Resume eval_all_type_sound_mutual[Log]:
  cheat
QED

Resume eval_all_type_sound_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
                       return_def, raise_def] >>
  gvs[AllCaseEqs(), option_CASE_rator, no_type_error_result_def]
  >- (
    `get_tenv cx = env.type_defs` by fs[env_consistent_def, env_context_consistent_def] >>
    gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
    gvs[lift_option_type_def, return_def, bind_apply] >>
    Cases_on `eval_expr cx e st` >>
    rename1 `eval_expr cx e st = (expr_res, st1)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st = (INL tvl, st1)` >>
      Cases_on `materialise cx tvl st1` >>
      rename1 `materialise cx tvl st1 = (mat_res, st2)` >>
      Cases_on `mat_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `materialise cx tvl st1 = (INL v, st2)` >>
        Cases_on `new_variable id x v st2` >>
        rename1 `new_variable id x v st2 = (new_res, st3)` >>
        Cases_on `new_res` >> gvs[bind_apply, ignore_bind_apply, return_def,
                                  no_type_error_result_def]
        >- (
          strip_tac >> gvs[] >>
          imp_res_tac materialise_state >> gvs[] >>
          `value_has_type x v` by (
            gvs[expr_runtime_typed_def] >>
            drule_at(Pat`materialise`) materialise_preserves_value_type >>
            simp[] >> disch_then irule >>
            drule evaluate_type_well_formed_type_value >> simp[]) >>
          conj_tac
          >- (irule new_variable_preserves_state_well_typed >>
              goal_assum(drule_at(Pat`new_variable`)) >>
              simp[] >> qexists_tac `cx` >> qexists_tac `expr_type e` >> simp[]) >>
          conj_tac >- (drule new_variable_accounts >> rw[]) >>
          drule_at(Pat`new_variable`) extend_local_env_consistent_after_new_variable >>
          simp[] >> disch_then irule >> simp[] >>
          goal_assum drule >> simp[]) >>
        strip_tac >> gvs[] >>
        imp_res_tac materialise_state >> gvs[] >>
        `value_has_type x v` by (
          gvs[expr_runtime_typed_def] >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          simp[] >> disch_then irule >>
          drule evaluate_type_well_formed_type_value >> simp[]) >>
        conj_tac
        >- (irule new_variable_preserves_state_well_typed_result >>
            goal_assum(drule_at(Pat`new_variable`)) >>
            simp[] >> qexists_tac `cx` >> qexists_tac `expr_type e` >> simp[]) >>
        conj_tac >- (drule new_variable_accounts >> rw[]) >>
        conj_asm1_tac
        >- (rpt strip_tac >> gvs[] >>
            drule_at(Pat`new_variable`) new_variable_no_type_error >>
            simp[] >> goal_assum drule_all) >>
        gvs[new_variable_def, bind_apply, AllCaseEqs(),
            ignore_bind_apply, list_CASE_rator, raise_def,
            get_scopes_def, return_def, type_check_def,
            assert_def, set_scopes_def]) >>
      strip_tac >> gvs[] >>
      drule materialise_state >> strip_tac >> gvs[] >>
      conj_tac
      >- (rpt strip_tac >> gvs[] >>
          gvs[expr_runtime_typed_def] >>
          drule_at_then Any drule
            materialise_typed_non_none_no_type_error >>
          simp[] >>
          metis_tac[evaluate_type_not_NoneT_imp_not_NoneTV]) >>
      drule materialise_no_control >>
      rw[no_control_exc_return_exception_typed]) >>
    strip_tac >> gvs[] >>
    drule eval_expr_exception_return_typed >> rw[]) >>
  rw[]
QED

Resume eval_all_type_sound_mutual[Append]:
  cheat
QED

Resume eval_all_type_sound_mutual[Assign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target cx tgt st` >>
  rename1 `eval_target cx tgt st = (target_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `target_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_target cx tgt st = (INL gv, st1)` >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res, st3)` >>
      Cases_on `mat_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v, st3)` >>
        Cases_on `assign_target cx gv (Replace v) st3` >>
        rename1 `assign_target cx gv (Replace v) st3 = (assign_res, st4)` >>
        Cases_on `assign_res` >> gvs[return_def, bind_apply, no_type_error_result_def]
        >- (
          imp_res_tac materialise_state >> gvs[] >>
          simp[bind_apply, ignore_bind_apply, return_def] >>
          strip_tac >> gvs[] >>
          drule_at(Pat`assign_target`)
            assign_target_preserves_state_well_typed >>
          simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
          disch_then drule >>
          simp[value_runtime_typed_def, expr_runtime_typed_def, PULL_EXISTS] >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          gvs[expr_runtime_typed_def] >>
          drule evaluate_type_well_formed_type_value >>
          strip_tac >>
          disch_then drule_all >> strip_tac >>
          disch_then $ drule_at Any >>
          disch_then $ drule_at Any >>
          strip_tac >>
          `target_runtime_typed env cx st2 tgt (expr_type e) gv` by (
            irule target_runtime_typed_rebuild >>
            simp[runtime_consistent_def] >>
            goal_assum drule) >>
          first_x_assum drule >> strip_tac >>
          conj_tac >- simp[] >>
          conj_tac >- simp[] >>
          drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent >>
          simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
          disch_then drule >>
          simp[value_runtime_typed_def, expr_runtime_typed_def] >>
          strip_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `tgt` >> qexists_tac `expr_type e` >> simp[] >>
          qexists_tac `tv` >> simp[]) >>
        qpat_x_assum `do _ od _ = _` mp_tac >> simp[bind_apply, return_def] >>
        Cases_on `res` >> gvs[ignore_bind_apply] >>
        strip_tac >> gvs[] >>
        strip_tac >> gvs[] >>
        imp_res_tac materialise_state >> gvs[] >>
        `?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
              value_has_type tv v /\ well_formed_type_value tv` by (
          gvs[expr_runtime_typed_def] >>
          drule evaluate_type_well_formed_type_value >> strip_tac >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          simp[] >> strip_tac >> goal_assum drule >> simp[]) >>
        `target_runtime_typed env cx st2 tgt (expr_type e) gv` by (
          irule target_runtime_typed_rebuild >>
          simp[runtime_consistent_def] >> goal_assum drule) >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_state_well_typed_result >>
        disch_then(drule_at Any) >>
        simp[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
        simp[runtime_consistent_def] >>
        strip_tac >>
        drule_all eval_expr_preserves_ec >> strip_tac >>
        conj_asm1_tac
        >- (rpt strip_tac >> gvs[] >>
            drule (cj 1 assign_target_no_type_error) >>
            simp[PULL_EXISTS] >>
            goal_assum(drule_at(Pat`assign_target`)) >> simp[] >>
            `get_tenv cx = env.type_defs` by gvs[env_consistent_def, env_context_consistent_def] >>
            gvs[] >>
            goal_assum(drule_at(Pat`evaluate_type`)) >> simp[] >>
            goal_assum drule >>
            simp[] >>
            drule eval_target_assignable >>
            disch_then drule >>
            strip_tac >>
            simp[]) >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_runtime_consistent_result >>
        simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
        simp[value_runtime_typed_def, PULL_EXISTS] >>
        disch_then(drule_at(Pat`target_runtime_typed`)) >> simp[] >>
        strip_tac >>
        Cases_on `y` >> rw[return_exception_typed_def] >>
        drule (cj 1 assign_target_no_return) >> simp[] >>
        disch_then drule >> simp[]) >>
      strip_tac >> gvs[] >>
      drule materialise_state >> strip_tac >> gvs[] >>
      conj_tac
      >- (rpt strip_tac >> gvs[] >>
          gvs[expr_runtime_typed_def] >>
          drule_at Any materialise_typed_non_none_no_type_error >> simp[] >>
          goal_assum drule >>
          drule evaluate_type_not_NoneT_imp_not_NoneTV >>
          simp[]) >>
      drule materialise_no_control >> rw[no_control_exc_return_exception_typed]) >>
    rw[] >> drule eval_expr_exception_return_typed >> rw[]) >>
  strip_tac >> gvs[] >>
  drule (cj 1 eval_target_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Resume eval_all_type_sound_mutual[AugAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (target_res, st1)` >>
  (* Apply base-target IH *)
  `type_place_target env bt = SOME (Type ty)` by fs[well_typed_target_def] >>
  qpat_x_assum `!env vt st res st'. _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_base_target _ _ _ = _ ==> _`
    (drule_at (Pat`type_place_target`)) >>
  simp[] >> strip_tac >>
  Cases_on `target_res`
  >- (
    fs[no_type_error_result_def] >>
    Cases_on `x` >> fs[] >> simp[bind_def] >>
    rename1 `eval_base_target cx bt st = (INL (loc,sbs), st1)` >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
    (* Apply expr IH via eval_base_target witness *)
    first_x_assum (qspecl_then [`st`, `loc`, `sbs`, `st1`] mp_tac) >> simp[] >>
    disch_then (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >>
    `state_well_typed st1 /\ env_consistent env cx st1 /\ accounts_well_typed st1.accounts` by (
      qpat_x_assum `!st' res st''. env_consistent _ _ st' /\ _ ==> _`
        (qspecl_then [`st`, `INL (loc,sbs)`, `st1`] mp_tac) >> simp[]) >>
    simp[] >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
      Cases_on `get_Value tvl st2` >>
      rename1 `get_Value tvl st2 = (val_res, st3)` >>
      Cases_on `val_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `get_Value tvl st2 = (INL v, st3)` >>
        imp_res_tac get_Value_state >> gvs[] >>
        `target_runtime_typed env cx st1 (BaseTarget bt) ty (BaseTargetV loc sbs)` by (
          drule_all eval_base_target_target_runtime_typed >> simp[]) >>
        `target_runtime_typed env cx st2 (BaseTarget bt) ty (BaseTargetV loc sbs)` by (
          metis_tac[target_runtime_typed_rebuild, runtime_consistent_def]) >>
        `tvl = Value v` by (
          qpat_x_assum `get_Value _ _ = _` mp_tac >>
          Cases_on `tvl` >> simp[get_Value_def, return_def, raise_def]) >>
        `assign_operation_runtime_typed env ty (Update ty bop v)` by (
          simp[assign_operation_runtime_typed_def] >>
          qexists_tac `expr_type e` >>
          gvs[expr_runtime_typed_def, value_runtime_typed_def,
              toplevel_value_typed_def]) >>
        simp[bind_apply, return_def] >>
        Cases_on `assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2` >>
        rename1 `assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2 = (assign_res, st4)` >>
        Cases_on `assign_res` >> simp[return_def, ignore_bind_def, no_type_error_result_def]
        >- (
          strip_tac >> gvs[] >>
          drule_at(Pat`assign_target`)
            assign_target_preserves_runtime_consistent >>
          disch_then $ drule_at(Pat`target_runtime_typed`) >>
          simp[] >>
          impl_keep_tac >- simp[runtime_consistent_def] >>
          strip_tac >>
          gvs[runtime_consistent_def, bind_def, return_def]) >>
        strip_tac >> gvs[] >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_runtime_consistent_result >>
        disch_then $ drule_at(Pat`target_runtime_typed`) >>
        simp[] >>
        impl_keep_tac >- simp[runtime_consistent_def] >>
        strip_tac >> gvs[runtime_consistent_def] >>
        `res = INR y /\ st' = st4` by (
          qpat_x_assum `do _ od _ = _` mp_tac >>
          simp[bind_def, return_def]) >>
        gvs[] >>
        Cases_on `y` >> rw[return_exception_typed_def]
        >- (spose_not_then strip_assume_tac >> gvs[] >>
            drule_at(Pat`assign_target`)assign_target_update_no_type_error >>
            disch_then drule >>
            disch_then(drule_at(Pat`well_typed_binop`)) >>
            disch_then drule >>
            simp[assign_target_assignable_def] >>
            CASE_TAC >>
            drule_at(Pat`eval_base_target`)eval_base_target_scoped_assignable >>
            simp[assign_target_assignable_def] >>
            disch_then irule >>
            goal_assum drule >>
            goal_assum drule ) >>
        drule (cj 1 assign_target_no_return) >> simp[] >>
        disch_then drule >> simp[]) >>
      strip_tac >> gvs[] >>
      imp_res_tac get_Value_state >> gvs[] >>
      drule get_Value_no_control >>
      strip_tac >> drule no_control_exc_return_exception_typed >>
      simp[] >>
      rpt strip_tac >> gvs[] >>
      gvs[expr_runtime_typed_def] >>
      drule_all well_typed_binop_not_In_second_type >> strip_tac >>
      drule_all evaluate_type_not_ArrayT_imp_not_ArrayTV >> strip_tac >>
      drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
      drule_all get_Value_no_type_error >>
      simp[no_type_error_result_def]) >>
    strip_tac >> gvs[] >>
    drule eval_expr_exception_return_typed >> rw[]) >>
  fs[no_type_error_result_def] >>
  strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule (cj 3 eval_target_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Resume eval_all_type_sound_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  rename1 `eval_expr cx e st = (cond_res, st1)` >>
  reverse(Cases_on `cond_res`)
  >- (
    strip_tac >>
    gvs[no_type_error_result_def] >>
    drule_all eval_expr_exception_return_typed >> simp[]
  ) >>
  simp_tac(srw_ss())[ignore_bind_def, bind_def] >>
  CASE_TAC >>
  reverse CASE_TAC >- (
    strip_tac >> gvs[] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[push_scope_def,return_def]
  ) >>
  rename1 `eval_expr cx e st = (INL tv, st1)` >>
  gvs[expr_runtime_typed_def, evaluate_type_def] >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  strip_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)` mp_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')` mp_tac >>
  simp[optionTheory.IS_SOME_EXISTS] >> ntac 2 strip_tac >>
  irule scope_bracket_post >>
  conj_asm1_tac >- (
    irule env_consistent_env_maps_wf >> simp[] >>
    goal_assum drule >> simp[]
  ) >>
  qmatch_asmsub_abbrev_tac`finally body pop_scope sf` >>
  qexistsl_tac[`body`,`st1`] >>
  simp[bind_def, ignore_bind_def] >>
  first_x_assum (drule_then drule) >> strip_tac >>
  last_x_assum (drule_then drule) >> strip_tac >>
  gvs[push_scope_def, return_def, finally_def] >>
  qmatch_goalsub_abbrev_tac`body st2` >>
  Cases_on`body st2` >> gvs[] >>
  qmatch_assum_rename_tac`body st2 = (rf,sf)` >>
  qho_match_abbrev_tac`P rf sf` >>
  irule switch_BoolV_post >>
  qunabbrev_tac`body` >>
  goal_assum $ drule_at(Pat`switch_BoolV`) >>
  simp[] >>
  `accounts_well_typed st2.accounts` by simp[Abbr`st2`] >>
  `env_consistent env cx st2` by (simp[Abbr`st2`] >> irule push_scope_env_consistent >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Abbr`P`] >>
    `state_well_typed st2` by gvs[Abbr`st2`, state_well_typed_def, scope_well_typed_def] >>
    first_x_assum drule_all >> strip_tac >>
    simp[] >>
    `st2 = st1 with scopes := FEMPTY::st1.scopes`
      by simp[evaluation_state_component_equality, Abbr`st2`] >>
    conj_tac >- (
      strip_tac >> gvs[] >>
      drule eval_stmts_preserves_scopes_len >> simp[]) >>
    Cases_on `res1` >> gvs[]
    >- (
      Cases_on `st1'.scopes` >> gvs[]
      >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
      irule type_stmts_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
        simp[] >> disch_then irule >>
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      conj_tac >- (
        qexists_tac `x` >>
        qexists_tac `ret_ty` >>
        qexists_tac `ss'` >> simp[] >>
        rpt strip_tac >> fs[] >>
        drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
        strip_tac >> gvs[FDOM_FEMPTY] >>
        drule lookup_scopes_is_some_same_fdoms >> simp[] >>
        disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
        qpat_x_assum `env_consistent env cx st1` mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
        strip_tac >> strip_tac >>
        Cases_on `lookup_scopes id t` >> gvs[] >>
        qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
          (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >>
      disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INL ()` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    conj_tac >- (
      irule env_extends_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>


      conj_tac >- (
        conj_tac >- (
          rpt strip_tac >> fs[] >>
          `?entry. lookup_scopes id st1.scopes = SOME entry` by (
            qpat_x_assum`env_consistent _ _ st1`mp_tac >>
            simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
          `FLOOKUP h id = NONE` suffices_by simp[] >>
          drule lookup_scopes_not_in_new_head >>
          disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
          simp[] >>
          disch_then irule >> simp[]) >>
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >>
        disch_then irule >> simp[]) >>
      conj_tac >- (
        qexists_tac `env_exn` >> simp[] >>
        rpt strip_tac >> fs[] >>
        `lookup_scopes id st1.scopes = NONE` by (
          qpat_x_assum`env_consistent env cx st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
          Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
          metis_tac[optionTheory.IS_SOME_DEF]) >>
        qspecl_then [`cx`, `ss'`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
          mp_tac eval_stmts_preserves_tail_lookup_none >>
        simp[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INR y`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >> disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INR y` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    irule env_extends_return_exception_typed >>
    qexists_tac `env_exn` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  simp[Abbr`P`] >>
  `state_well_typed st2` by gvs[Abbr`st2`, state_well_typed_def, scope_well_typed_def] >>
  first_x_assum drule_all >> strip_tac >>
  simp[] >>
  `st2 = st1 with scopes := FEMPTY::st1.scopes`
    by simp[evaluation_state_component_equality, Abbr`st2`] >>
  conj_tac >- (
    strip_tac >> gvs[] >>
    drule eval_stmts_preserves_scopes_len >> simp[]) >>
  Cases_on `res1` >> gvs[]
  >- (
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    irule type_stmts_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
      simp[] >> disch_then irule >>
      qpat_x_assum`env_consistent _ _ st1`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    conj_tac >- (
      qexists_tac `x'` >>
      qexists_tac `ret_ty` >>
      qexists_tac `ss` >> simp[] >>
      rpt strip_tac >> fs[] >>
      drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
      strip_tac >> gvs[FDOM_FEMPTY] >>
      drule lookup_scopes_is_some_same_fdoms >> simp[] >>
      disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
      qpat_x_assum `env_consistent env cx st1` mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
      strip_tac >> strip_tac >>
      Cases_on `lookup_scopes id t` >> gvs[] >>
      qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
        (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INL x''`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >>
    disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INL x''` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  Cases_on `st1'.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  conj_tac >- (
    irule env_extends_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >> disch_then irule >> simp[]) >>
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st1.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      drule lookup_scopes_not_in_new_head >>
      disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
    conj_tac >- (
      qexists_tac `env_exn` >> simp[] >>
      rpt strip_tac >> fs[] >>
      `lookup_scopes id st1.scopes = NONE` by (
        qpat_x_assum`env_consistent env cx st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
        Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
        metis_tac[optionTheory.IS_SOME_DEF]) >>
      qspecl_then [`cx`, `ss`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
        mp_tac eval_stmts_preserves_tail_lookup_none >>
      simp[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INR y`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >> disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INR y` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_all_type_sound_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[] >>
    drule_all expr_runtime_typed_hashmap_ref_place >> simp[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[Stmts_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, Once evaluate_def,
      return_def, no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  last_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (
    Cases_on `eval_stmts cx ss st1` >>
    rename1 `eval_stmts cx ss st1 = (r2,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    strip_tac >> fs[bind_def] >> gvs[] >>
    Cases_on `r2` >> gvs[no_type_error_result_def]
    >- (
      qexists_tac `env_exn` >> simp[] >>
      irule env_extends_trans >>
      qexists_tac `env''` >> simp[] >>
      irule type_stmt_env_extends >> simp[] >>
      conj_tac >- (irule env_consistent_env_maps_wf >> goal_assum drule >> simp[]) >>
      qexists_tac `ret_ty` >> qexists_tac `s` >> simp[]) >>
    simp[]) >>
  strip_tac >> gvs[] >>
  qexists_tac `env` >> simp[env_extends_refl]
QED

Resume eval_all_type_sound_mutual[For]:
  cheat
QED

Resume eval_all_type_sound_mutual[For_nil]:
  cheat
QED

Resume eval_all_type_sound_mutual[For_cons]:
  cheat
QED

Resume eval_all_type_sound_mutual[Iterator_Array]:
  cheat
QED

Resume eval_all_type_sound_mutual[Iterator_Range]:
  cheat
QED

Resume eval_all_type_sound_mutual[Target_Base]:
  cheat
QED

Resume eval_all_type_sound_mutual[Target_Tuple]:
  cheat
QED

Resume eval_all_type_sound_mutual[Targets_nil]:
  cheat
QED

Resume eval_all_type_sound_mutual[Targets_cons]:
  cheat
QED

Resume eval_all_type_sound_mutual[BaseTarget_Name]:
  cheat
QED

Resume eval_all_type_sound_mutual[BaseTarget_BareGlobal]:
  cheat
QED

Resume eval_all_type_sound_mutual[BaseTarget_TopLevel]:
  cheat
QED

Resume eval_all_type_sound_mutual[BaseTarget_Subscript]:
  cheat
QED

Resume eval_all_type_sound_mutual[BaseTarget_Attribute]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Name]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_BareGlobalName]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_TopLevelName]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_FlagMember]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_IfExp]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Literal]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_StructLit]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Subscript]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Attribute]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Builtin]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_TypeBuiltin]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Pop]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_IntCall]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_Send]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawLog]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawRevert]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_SelfDestructTarget]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_CreateTarget]:
  cheat
QED

Resume eval_all_type_sound_mutual[Exprs_nil]:
  cheat
QED

Resume eval_all_type_sound_mutual[Exprs_cons]:
  cheat
QED

Finalise eval_all_type_sound_mutual

Theorem eval_stmt_no_type_error:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmt cx s st)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx s st` >>
  simp[no_type_error_eval_def] >>
  drule_all (cj 1 eval_all_type_sound_mutual) >> rw[]
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

