Theory bodyIntCallPostObservation
Ancestors
  bodyIntCallObserverFrame exprSimHash loweringPosts exprLoweringProps venomState compileEnv abiEncoderObserver

Theorem eval_operand_returndata[local]:
  eval_operand op (s with vs_returndata := data) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem vv_post_returndata:
  vv_post ctx func cenv cx e es sa sb start es' raw vv
    (s with vs_returndata := data) <=>
  vv_post ctx func cenv cx e es sa sb start es' raw vv s
Proof
  Cases_on `vv` >>
  simp[vv_post_def, hash_returndata_state_rel, vv_holds_def, vv_at_def,
       eval_operand_returndata,
       expr_val_rel_def, expr_val_at_def, storage_holds_def,
       contract_storage_def, contract_transient_def, eval_operand_def,
       lookup_var_def, local_region_def, locals_kept_def]
QED

Theorem vv_post_stop_view:
  vv_post ctx func cenv cx e es sa sb start es' raw vv v /\
  stop_view u = stop_view v /\ ~u.vs_halted /\ ~v.vs_halted ==>
  vv_post ctx func cenv cx e es sa sb start es' raw vv u
Proof
  strip_tac >>
  `u = v with vs_returndata := u.vs_returndata` by
    gvs[stop_view_def, halt_state_def, venom_state_component_equality] >>
  qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  simp[vv_post_returndata]
QED

