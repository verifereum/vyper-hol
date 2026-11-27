(* The source hand-off at a qualified internal call. *)
Theory bodyIntCallSourceBindMods
Ancestors
  exprSimDefs gasContext list vyperContext vyperInterpreter vyperState
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

Theorem selected_source_bind_values_mods:
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
