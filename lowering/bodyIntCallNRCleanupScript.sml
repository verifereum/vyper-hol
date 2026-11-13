(* Source cleanup after acquisition, with the halt exemption kept explicit. *)
Theory bodyIntCallNRCleanup
Ancestors
  bodyIntCallNRCleanupProbe bodyIntCallNRSource bodyIntCallSeamDefs
  gasContext exprSimDefs exprLoweringProps loweringHalt vyperTyping vyperInterpreter vyperState
Libs
  monadsyntax

Theorem intcall_rest_lock_failure:
  lock_if_nr cx nr (is_view_mut mut) es = (INR ex,ee) ==>
  intcall_rest cx name mut nr ss prev rtv es = (INR ex,ee)
Proof
  strip_tac >> simp[intcall_rest_def, ignore_bind_def, bind_def,
                    Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_rest_acquired:
  lock_if_nr cx nr (is_view_mut mut) es = (INL (),ls) /\
  (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
           return NoneV od) handle_function) ls = (res,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ue) ==>
  intcall_rest cx name mut nr ss prev rtv es =
    bind (\st. (res, if res = INR HaltException then ee with scopes := prev
                    else ue with scopes := prev))
      (\rv. do crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
               return (Value crv) od) es
Proof
  strip_tac >> drule_all intcall_cleanup_terminal >> strip_tac >>
  fs[ignore_bind_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  simp[intcall_rest_def, ignore_bind_def, bind_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_unlock_gas_obs:
  unlock_if_nr cx nr view (es with gas_obs := gs) =
    let (res,ee) = unlock_if_nr cx nr view es in
      (res,ee with gas_obs := gs)
Proof
  Cases_on `nr /\ ~view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_def,
       get_transient_storage_def, update_transient_def, bind_def, return_def]
QED

Theorem intcall_unlock_total:
  ?ue. unlock_if_nr cx nr view es = (INL (),ue)
Proof
  Cases_on `nr /\ ~view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, release_nonreentrant_lock_def,
       get_transient_storage_def, update_transient_def, bind_def, return_def]
QED

Theorem intcall_rest_normal:
  intcall_callee_src cx name mut nr ss es = (INL v,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ue) ==>
  intcall_rest cx name mut nr ss prev rtv es =
    (do crv <- lift_option_type (safe_cast rtv v) "IntCall cast ret";
        return (Value crv) od) (ue with scopes := prev)
Proof
  strip_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) es` >>
  rename1 `_ = (lr,ls)` >> Cases_on `lr` >>
  gvs[intcall_callee_src_def, ignore_bind_def, bind_def,
      Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  rename1 `lock_if_nr _ _ _ _ = (INL u,ls)` >>
  Cases_on `u` >>
  drule_all intcall_cleanup_terminal >> strip_tac >>
  simp[intcall_rest_def, ignore_bind_def, bind_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem intcall_rest_normal_typed:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es /\
  intcall_callee_src cx name mut nr ss (es with gas_obs := gs) = (INL v,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ue) ==>
  value_has_type rtv v /\
  intcall_rest cx name mut nr ss prev rtv (es with gas_obs := gs) =
    (INL (Value v),ue with scopes := prev)
Proof
  strip_tac >> drule_all intcall_rest_normal >> strip_tac >>
  Cases_on `safe_cast rtv v`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `gs` mp_tac) >>
      simp[bind_def, lift_option_type_def, raise_def, expr_vv_res_ok_def]) >>
  rename1 `safe_cast rtv v = SOME cv` >>
  `value_has_type rtv cv` by (drule safe_cast_result_well_typed >> simp[]) >>
  drule (cj 1 safe_cast_some_eq) >> strip_tac >> gvs[] >>
  simp[bind_def, lift_option_type_def, return_def]
QED

Theorem intcall_marked_return_typed:
  gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es /\
  gas_marked_exec memory (ctx,callee) (intcall_callee_src cx name mut nr ss)
    (es,entered) marks (INL v) ee r ==>
  value_has_type rtv v
Proof
  strip_tac >> fs[gasSummaryTheory.gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `?ue. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) =
          (INL (),ue)` by metis_tac[intcall_unlock_total] >>
  drule_all intcall_rest_normal_typed >> simp[]
QED
