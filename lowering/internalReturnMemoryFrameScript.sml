(* Source and result frames retained for the joint internal Return. *)
Theory internalReturnMemoryFrame
Ancestors
  stmtLowering loweringPosts exprLoweringProps compileEnv bodySim
  loweringStateRelDefs stmtSimReturn venomState vyperState intCallReturnMem

Theorem internal_return_exit_stmt_state_rel:
  same_frame cenv cenv' /\ stmt_state_rel H ctx func cenv' cx es s ==>
  stmt_state_rel H ctx func cenv cx (es with scopes := []) s
Proof
  strip_tac >>
  `state_rel H func cenv cx (es with scopes := []) s` by
    (irule constructor_exit_state_rel >> qexists_tac `cenv'` >>
     fs[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
     immutable_base_zero_def, same_frame_def, compile_env_component_equality,
     lookup_scopes_def, local_region_def] >> metis_tac[]
QED

Theorem internal_return_post_frame:
  same_frame cenv ce /\ intret_q H func ce cx tv v (ee with scopes := []) r ==>
  intret_q H func cenv cx tv v (ee with scopes := []) r
Proof
  rw[intret_q_def] >>
  `ce.ce_nonreentrant = cenv.ce_nonreentrant /\
   ce.ce_returns_count = cenv.ce_returns_count` by
    fs[same_frame_def, compile_env_component_equality] >>
  qexistsl_tac [`s`, `i`] >> gvs[return_unlock_state_def, result_rel_def] >>
  drule_all constructor_exit_state_rel >> simp[]
QED
