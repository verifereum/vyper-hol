(* Compilation intervals for a selected packaged external body. *)
Theory selectedBodyCode
Ancestors actualRegistrationCode moduleLowering compileEnv
  loweringShapeDefs loweringShapeRules loweringShapeProps fragExec list

Theorem external_selected_body_boundary:
  compile_external_fn_bodies
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix)
    st = ((),stf) /\ shape_state st /\
  EVERY external_fn_shape_ok
    (prefix ++ (lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type) :: suffix) ==>
  ?first ce registered body_end.
    compile_register_positional_args cenv args 4 first = (ce,registered) /\
    compile_guarded_body ce nr nkey transient view ss ret_type registered = ((),body_end) /\
    shape_state registered /\ cs_extends st first /\
    cs_extends registered body_end /\ cs_extends body_end stf
Proof
  strip_tac >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  rewrite_tac[external_bodies_append] >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies (_::_) _ = _` mp_tac >>
  pure_once_rewrite_tac[external_bodies_cons_split] >> strip_tac >>
  fs[EVERY_APPEND] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_singleton_body_boundary >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies prefix _ = _` kall_tac >>
  `EVERY external_fn_shape_ok
    [(lbl,cenv,args,min_cds,pay,nr,nkey,transient,view,ss,ret_type)]` by simp[] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  qpat_x_assum `compile_external_fn_bodies [_] _ = _` kall_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  fs[external_fn_shape_ok_def] >>
  drule_all external_function_registration_boundary >> strip_tac >>
  goal_assum $ drule_at Any >> metis_tac[cs_extends_trans]
QED
