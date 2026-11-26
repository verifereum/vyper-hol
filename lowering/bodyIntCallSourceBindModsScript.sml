(* The source hand-off at a qualified internal call. *)
Theory bodyIntCallSourceBindMods
Ancestors
  bodyBranchCellFrameMods bodyFullPredsMods constSubstCorrect constSubstStmts
  exprSimDefs exprSimHypsDefs gasContext list
  vyperContext vyperInterpreter vyperLookupStorage vyperState vyperTypeInvariants
Libs
  monadsyntax

(* The lock was taken in the caller state, before installing these scopes. *)
Definition intcall_after_push_mods_def:
  intcall_after_push_mods cx key mut nr ss prev rtv = do
    rv <- finally_unless_halt
      (finally
        (try (do eval_stmts (cx with stk updated_by CONS key) ss; return NoneV od)
             handle_function)
        (pop_function prev))
      (unlock_if_nr cx nr (is_view_mut mut));
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return (Value crv)
  od
End

Theorem selected_source_call_step_mods:
  ~MEM (src,name) cx.stk /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts ==>
  eval_expr cx (Call ann (IntCall (src,name)) es dflt) st =
  case eval_exprs cx es st of
    (INR err,mid) => (INR err,mid)
  | (INL vs,mid) =>
      case eval_exprs (cx with stk updated_by CONS (src,name))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             (mid with scopes := [FEMPTY]) of
        (INR err,fin) => (INR err,fin with scopes := mid.scopes)
      | (INL dvs,fin) =>
        let restored = fin with scopes := mid.scopes in
        case bind_arguments (get_tenv cx) args (vs ++ dvs) of
          NONE => (INR (Error (TypeError "IntCall bind_arguments")),restored)
        | SOME penv =>
          case evaluate_type (get_tenv cx) ret of
            NONE => (INR (Error (TypeError "IntCall eval ret")),restored)
          | SOME rtv =>
            case lock_if_nr cx nr (is_view_mut mut) restored of
              (INR err,locked) => (INR err,locked)
            | (INL u,locked) =>
              intcall_after_push_mods cx (src,name) mut nr ss mid.scopes rtv
                (locked with scopes := [penv])
Proof
  strip_tac >>
  `LENGTH args <= LENGTH es + LENGTH dflts` by decide_tac >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (actual,mid)` >>
  Cases_on `actual` >>
  asm_simp_tac std_ss [Once evaluate_def, ignore_bind_apply, bind_apply,
    type_check_def, assert_def, lift_option_type_def, return_def, get_scopes_def,
    pairTheory.pair_case_thm, pairTheory.FST, pairTheory.SND,
    sumTheory.sum_case_def, optionTheory.option_case_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `eval_exprs p ds (mid with scopes := [FEMPTY])` >>
  Cases_on `eval_exprs p ds (mid with scopes := [FEMPTY])` >>
  rename1 `eval_exprs p ds _ = (defs,fin)` >> Cases_on `defs` >>
  asm_simp_tac std_ss [finally_def, set_scopes_def, ignore_bind_apply, bind_apply,
    return_def, raise_def, pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  qmatch_goalsub_abbrev_tac `bind_arguments (get_tenv cx) args vals` >>
  Cases_on `bind_arguments (get_tenv cx) args vals` >>
  asm_simp_tac std_ss [optionTheory.option_case_def, return_def, raise_def,
    pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  Cases_on `evaluate_type (get_tenv cx) ret` >>
  asm_simp_tac std_ss [optionTheory.option_case_def, return_def, raise_def,
    pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  qmatch_goalsub_abbrev_tac `lock_if_nr cx nr (is_view_mut mut) restored` >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) restored` >>
  rename1 `lock_if_nr _ _ _ _ = (taken,locked)` >> Cases_on `taken` >>
  asm_simp_tac std_ss [push_function_def, return_def, intcall_after_push_mods_def,
    bind_apply, ignore_bind_apply, lift_option_type_def, pairTheory.pair_case_thm,
    sumTheory.sum_case_def]
QED

Theorem selected_source_bind_values_mods[local]:
  ~MEM (src,name) cx.stk /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts /\
  gas_admissible (eval_expr cx (Call ann (IntCall (src,name)) es dflt)) expr_vv_res_ok st /\
  eval_exprs cx es (st with gas_obs := obs) = (INL vs,mid) /\
  eval_exprs (cx with stk updated_by CONS (src,name))
    (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
    (mid with scopes := [FEMPTY]) = (INL dvs,fin) ==>
  ?penv rtv. bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
             evaluate_type (get_tenv cx) ret = SOME rtv
Proof
  strip_tac >>
  drule_all selected_source_call_step_mods >>
  disch_then (qspecl_then [`st with gas_obs := obs`,`dflt`,`ann`] mp_tac) >>
  asm_simp_tac std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def, LET_THM] >>
  Cases_on `bind_arguments (get_tenv cx) args (vs ++ dvs)`
  >- (simp[optionTheory.option_case_def] >> strip_tac >>
      drule_all gas_admissible_result >> simp[expr_vv_res_ok_def]) >>
  Cases_on `evaluate_type (get_tenv cx) ret` >> simp[] >>
  strip_tac >> drule_all gas_admissible_result >> simp[expr_vv_res_ok_def]
QED

(* The defaults run in a different scope and call stack.  Only their
   dynamic typing facts are used when restoring the caller. *)
Theorem selected_default_inv_restore_mods[local]:
  expr_sim_inv_mods mods ce cx env mid /\
  expr_sim_inv_mods mods cde (cx with stk := stack) envd fin /\
  envd.bare_globals = env.bare_globals /\
  envd.toplevel_vtypes = env.toplevel_vtypes ==>
  expr_sim_inv_mods mods ce cx env (fin with scopes := mid.scopes)
Proof
  rewrite_tac[expr_sim_inv_mods_def, env_consistent_def] >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[evaluation_state_accfupds, combinTheory.K_THM] >>
  TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `env_scopes_consistent env cx mid` mp_tac >>
      pure_rewrite_tac[env_scopes_consistent_def, evaluation_state_accfupds, combinTheory.K_THM] >>
      disch_then ACCEPT_TAC)
  >- (qpat_assum `env_immutables_consistent envd _ fin` mp_tac >>
      qpat_assum `envd.bare_globals = _` (fn bg =>
        qpat_assum `envd.toplevel_vtypes = _` (fn vt =>
          pure_rewrite_tac[bg, vt, env_immutables_consistent_def,
            evaluation_state_accfupds, evaluation_context_accfupds,
            get_tenv_stk, get_module_code_stk])) >> disch_then ACCEPT_TAC) >>
  qpat_assum `state_well_typed fin` mp_tac >>
  qpat_assum `state_well_typed mid` mp_tac >>
  pure_rewrite_tac[state_well_typed_def, evaluation_state_accfupds, combinTheory.K_THM] >>
  rpt strip_tac >> first_assum ACCEPT_TAC
QED

Theorem selected_default_cells_restore_mods[local]:
  body_const_cells_agree_mods mods cx env mid /\
  body_const_cells_agree_mods mods (cx with stk := stack) envd fin /\
  envd.bare_globals = env.bare_globals /\
  envd.toplevel_vtypes = env.toplevel_vtypes ==>
  body_const_cells_agree_mods mods cx env fin
Proof
  strip_tac >>
  qpat_x_assum `body_const_cells_agree_mods mods cx env mid`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  qpat_x_assum `body_const_cells_agree_mods mods (cx with stk := stack) envd fin`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [body_const_cells_agree_mods_def, get_tenv_stk]) >>
  gvs[] >>
  qpat_assum `const_cells_agree _ fin` (fn th =>
    pure_rewrite_tac[body_const_cells_agree_mods_def] >> irule_at Any th) >>
  qpat_assum `check_contract _ _ _ _ = SOME _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!addr src id tv root. MEM _ roots' ==> _` drule >>
      simp[checked_frame_context_def]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!src id r. _ ==> declared_constant _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[] >> qexistsl [`pv`,`v`] >>
  conj_tac
  >- (qpat_assum `const_result_at _ _ _ (PlaceR (ImmutablePlace _ _ [])) _` mp_tac >>
      pure_rewrite_tac[const_result_at_def, evaluation_context_accfupds, get_tenv_stk] >>
      disch_then ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `const_result_at _ _ _ pv v` mp_tac >>
      pure_rewrite_tac[const_result_at_def, evaluation_context_accfupds, get_tenv_stk] >>
      disch_then ACCEPT_TAC) >>
  drule_then (fn eq =>
    qpat_assum `!st. const_cells_agree roots' st ==> _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [eq, lookup_global_stk])) constant_expr_eval_stk
QED

(* The staged state is before the nonreentrancy lock.  The source body
   uses the result of taking the lock, not the staged state alone. *)
Theorem selected_source_bind_mods:
  ~MEM (src,name) cx.stk /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts /\
  gas_admissible (eval_expr cx (Call ann (IntCall (src,name)) es dflt)) expr_vv_res_ok st /\
  eval_exprs cx es (st with gas_obs := obs) = (INL vs,mid) /\
  eval_exprs (cx with stk updated_by CONS (src,name))
    (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
    (mid with scopes := [FEMPTY]) = (INL dvs,fin) /\
  expr_sim_inv_mods mods ce cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  expr_sim_inv_mods mods cde (cx with stk updated_by CONS (src,name)) envd fin /\
  body_const_cells_agree_mods mods (cx with stk updated_by CONS (src,name)) envd fin /\
  envd.bare_globals = env.bare_globals /\ envd.toplevel_vtypes = env.toplevel_vtypes ==>
  ?prev penv rtv es1.
    prev = mid.scopes /\
    bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    es1 = fin with scopes := [penv] /\ es1.scopes = [penv] /\
    expr_sim_inv_mods mods ce cx env (es1 with scopes := prev) /\
    body_const_cells_agree_mods mods cx env es1 /\
    eval_expr cx (Call ann (IntCall (src,name)) es dflt) (st with gas_obs := obs) =
      case lock_if_nr cx nr (is_view_mut mut) (es1 with scopes := prev) of
        (INR err,locked) => (INR err,locked)
      | (INL u,locked) =>
          intcall_after_push_mods cx (src,name) mut nr ss prev rtv
            (locked with scopes := [penv])
Proof
  strip_tac >> drule_all_then strip_assume_tac selected_source_bind_values_mods >>
  qexistsl [`mid.scopes`,`penv`,`rtv`,`fin with scopes := [penv]`] >>
  asm_simp_tac std_ss [evaluation_state_accfupds, combinTheory.K_THM,
    evaluation_state_fupdfupds, body_const_cells_agree_mods_branch_updates] >>
  `cx with stk updated_by CONS (src,name) = cx with stk := (src,name)::cx.stk` by
    simp[NoAsms, evaluation_context_component_equality] >>
  conj_tac
  >- (irule selected_default_inv_restore_mods >>
      rpt (first_assum (irule_at Any)) >> qexistsl [`(src,name)::cx.stk`,`cde`] >>
      qpat_assum `_ = cx with stk := _` (fn th => pure_rewrite_tac[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule selected_default_cells_restore_mods >>
      rpt (first_assum (irule_at Any)) >> qexists `(src,name)::cx.stk` >>
      qpat_assum `_ = cx with stk := _` (fn th => pure_rewrite_tac[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ = cx with stk := _` kall_tac >>
  drule_all selected_source_call_step_mods >>
  disch_then (qspecl_then [`st with gas_obs := obs`,`dflt`,`ann`] mp_tac) >>
  asm_simp_tac std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def,
    optionTheory.option_case_def, LET_THM]
QED
