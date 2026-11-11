Theory bodyIntCallReturnSource
Ancestors
  bodyIntCallImmutableFrame vyperInterpreter vyperState
  gasContext exprSimDefs vyperTyping loweringHalt
Libs
  monadsyntax

Theorem function_body_immutable_alloca_sep:
  (try (do eval_stmts cxf ss; return NoneV od) handle_function) es =
    (res,ee) /\
  immutable_alloca_sep func cenv cx (es with scopes := prev) s ==>
  immutable_alloca_sep func cenv cx (ee with scopes := prev) s
Proof
  Cases_on `eval_stmts cxf ss es` >> rename1 `_ = (br,be)` >>
  Cases_on `br` >>
  simp[bind_def, ignore_bind_def, return_def, try_def] >>
  rpt strip_tac
  >- (gvs[] >> drule_all eval_stmts_immutable_alloca_sep >> simp[]) >>
  rename1 `handle_function ex be` >>
  Cases_on `ex` >> gvs[handle_function_def, return_def, raise_def] >>
  drule_all eval_stmts_immutable_alloca_sep >> simp[]
QED

Theorem function_cleanup_result:
  f es = (res,ee) ==>
  finally f (do pop_function prev; unlock_if_nr cx F view od) es =
    (res,ee with scopes := prev)
Proof
  strip_tac >> Cases_on `res` >>
  simp[finally_def, pop_function_def, unlock_if_nr_def,
       set_scopes_def, ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem function_cleanup_cast_return:
  gas_admissible
    (do rv <- finally f
          (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od) expr_vv_res_ok es /\
  f (es with gas_obs := gs) = (INL v,ee) ==>
  ?crv. safe_cast rtv v = SOME crv /\ value_has_type rtv crv /\
    (do rv <- finally f
          (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od) (es with gas_obs := gs) =
      (INL (Value crv),ee with scopes := prev)
Proof
  strip_tac >> drule function_cleanup_result >>
  disch_then (qspecl_then [`view`,`prev`,`cx`] assume_tac) >>
  Cases_on `safe_cast rtv v`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `gs` mp_tac) >>
      simp[bind_def, lift_option_type_def, raise_def,
           expr_vv_res_ok_def]) >>
  rename1 `safe_cast rtv v = SOME crv` >>
  qexists_tac `crv` >> simp[bind_def, lift_option_type_def, return_def] >>
  drule safe_cast_result_well_typed >> simp[]
QED

Theorem function_cleanup_cast_raise:
  f es = (INR ex,ee) ==>
  (do rv <- finally f
        (do pop_function prev; unlock_if_nr cx F view od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv) od) es = (INR ex,ee with scopes := prev)
Proof
  strip_tac >> drule function_cleanup_result >>
  disch_then (qspecl_then [`view`,`prev`,`cx`] assume_tac) >>
  simp[bind_def]
QED

Theorem function_cleanup_return_typed:
  gas_admissible
    (do rv <- finally f
          (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od) expr_vv_res_ok es /\
  f (es with gas_obs := gs) = (INL v,ee) ==>
  value_has_type rtv v /\
    (do rv <- finally f
          (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od) (es with gas_obs := gs) =
      (INL (Value v),ee with scopes := prev)
Proof
  strip_tac >> drule_all function_cleanup_cast_return >> strip_tac >>
  drule (cj 1 safe_cast_some_eq) >> strip_tac >> gvs[]
QED
