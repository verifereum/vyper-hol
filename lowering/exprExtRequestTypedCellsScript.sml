(* Convert delayed-read runtime typing into the fixed-root tuple interface. *)
Theory exprExtRequestTypedCells
Ancestors
  exprExtRequestDelayedTyping exprExtRequestTupleFold exprExtRequestTyping
  exprExtRequestDefaultProbe exprSimHyps exprSimHypsDefs
  memoryLocalRhsProps valueEncodingTyping abiValueEncoding allocLimits
  vyperTypeSystem vyperValue compileEnv words list vyperState
  exprExtRequestStrongCapture exprExtRequestKwargs exprExtRequestUnreadCps
  exprExtRequestHistory exprExtRequestReadProbe exprExtRequestStagesSource

Theorem extrequest_typed_cell:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  extrequest_strong_capture ctx func cenv cx e r vv ee sb t /\
  read_result cx r ee = (INL v,ee) /\
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type cenv e) v ==>
  ?tv. extrequest_tuple_cell ctx func cenv cx ee sb t ee
    (e,r,vv,lowered_value_type cenv e,tv,v)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
   alloc_limits_expr cenv e` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv` >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[memory_rhs_runtime_layout, optionTheory.IS_SOME_DEF] >>
  `!stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
     ~is_word_type (expr_type e) ==>
     type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
     type_memory_size stv < 2**64` by
    (rpt strip_tac >>
     drule_all expr_sim_inv_memory_size >> strip_tac >>
     drule alloc_limits_expr_type_alloc_ok >>
     simp[type_alloc_ok_def]) >>
  `type_memory_size tv < dimword (:256)` by
    (Cases_on `is_word_type (lowered_value_type cenv e)`
     >- (drule_all abi_word_type_size >> simp[dimword_def]) >>
     drule_all extrequest_default_copy_capacity >> simp[]) >>
  qexists_tac `tv` >> simp[extrequest_tuple_cell_def] >>
  metis_tac[extrequest_lowered_type_compatible, value_has_type_val_wf]
QED

Theorem extrequest_typed_cells:
  !xs rs vvs vs.
  EVERY (\e. expr_body_pre cenv cx env e es /\ ~expr_has_effect e) xs /\
  extrequest_strong_captures ctx func cenv cx xs rs vvs ee sb t /\
  read_results cx rs ee = (INL vs,ee) /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type cenv e) v) xs vs ==>
  ?cells.
    EVERY (extrequest_tuple_cell ctx func cenv cx ee sb t ee) cells /\
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells =
      ZIP (vvs, MAP (lowered_value_type cenv) xs) /\
    MAP (\(e,r,vv,ty,tv,v). v) cells = vs /\
    MAP (\(e,r,vv,ty,tv,v). ty) cells = MAP (lowered_value_type cenv) xs
Proof
  Induct
  >- (simp[extrequest_strong_captures_def] >> rpt strip_tac >>
      gvs[] >> simp[ZIP_def]) >>
  rpt gen_tac >> Cases_on `rs` >> Cases_on `vvs` >> Cases_on `vs` >>
  simp[extrequest_strong_captures_def] >> strip_tac >>
  gvs[read_results_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  drule read_result_state >> disch_then SUBST_ALL_TAC >>
  `?tv. extrequest_tuple_cell ctx func cenv cx ee sb t ee
      (h,h',h'',lowered_value_type cenv h,tv,h''')` by
    (irule extrequest_typed_cell >> metis_tac[]) >>
  first_x_assum (qspecl_then [`t'`, `t''`, `t'''`] mp_tac) >>
  impl_tac >- simp[extrequest_strong_captures_def] >> strip_tac >>
  qexists_tac `(h,h',h'',lowered_value_type cenv h,tv,h''')::cells` >> simp[]
QED

Theorem extrequest_kwargs_typed_cells:
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  EVERY (\e. ~expr_has_effect e) xs /\
  expr_sim_inv cenv cx env start /\
  extrequest_results_success cx xs start rs pos_end /\
  extrequest_kwargs_post ctx func cenv cx rt opts kwargs pos_end s2 t2 s3
    value_op gas_op default_op xs rs arg_vvs kwvs ee t /\
  read_results cx rs ee = (INL vs,ee) ==>
  ?cells.
    EVERY (extrequest_tuple_cell ctx func cenv cx ee s3 t ee) cells /\
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells =
      ZIP (arg_vvs, MAP (lowered_value_type cenv) xs) /\
    MAP (\(e,r,vv,ty,tv,v). v) cells = vs /\
    MAP (\(e,r,vv,ty,tv,v). ty) cells = MAP (lowered_value_type cenv) xs
Proof
  strip_tac >>
  `extrequest_strong_captures ctx func cenv cx xs rs arg_vvs ee s3 t /\
   extrequest_read_frame cx (pos_end with gas_obs := []) ee` by
    fs[extrequest_kwargs_post_def, extrequest_history_frame_def] >>
  qpat_x_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
  simp[extrequest_results_success_def] >> strip_tac >>
  `extrequest_read_frame cx mid ee` by
    fs[extrequest_read_frame_def] >>
  `LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
      value_runtime_typed env (lowered_value_type cenv e) v) xs vs` by
    (irule extrequest_delayed_results_typed >>
     first_assum (irule_at (Pat `eval_expr_results _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  irule extrequest_typed_cells >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`env`, `start`] >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED
