(* Shared compilation and runtime frame interfaces for internal returns. *)
Theory internalReturnBoundaryCommonMem
Ancestors
  bodyMemoryDefs stmtLowering loweringPosts exprLoweringProps compileEnv
  ctorReturnFrame bodySim loweringStateRelDefs stmtSimReturn stmtSimDefs
  externalReturnPrefix stmtLoweringMono exprOperandVar loweringShapeDefs
  fragExec venomState vyperState intCallReturnMem

Theorem internal_return_value_compile:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  lower_value compile_expr cenv ty e sa = (op,s1) ==>
  compile_internal_return_from_env cenv ty (lowered_value_type cenv e)
    op (Var rpc) s1 = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

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
  qexists_tac `s` >> gvs[return_unlock_state_def, result_rel_def] >>
  drule_all constructor_exit_state_rel >> simp[]
QED

Theorem internal_return_value_preparation:
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr ce ty e sa = (op,s1) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\ ret_pc_ok ce sa s0 /\
  expr_post H ctx func ce cx e es sa s1 s0 ee v op t ==>
  compile_internal_return_from_env ce ty (lowered_value_type ce e)
    op (Var rpc) s1 = ((),sb) /\
  fn_has_code s1 sb func /\
  (?pc. eval_operand (Var rpc) t = SOME pc) /\
  (!x. op = Var x ==> not_fresh_at s1 x) /\
  (!x. Var rpc = Var x ==> not_fresh_at s1 x) /\
  stmt_state_rel H ctx func ce cx (ee with scopes := []) t
Proof
  strip_tac >>
  `cs_extends sa s1` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `cs_extends s1 sb` by metis_tac[return_value_code_prefix] >>
  `fn_has_code s1 sb func` by metis_tac[fn_has_code_split] >>
  `?pc. eval_operand (Var rpc) t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def, eval_operand_def] >> metis_tac[]) >>
  `!x. Var rpc = Var x ==> not_fresh_at s1 x` by
    (simp[] >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> conj_tac
     >- metis_tac[ci_mono_lower_value_compile_expr, ci_mono_def, pairTheory.SND] >>
     fs[ret_pc_ok_def] >> first_x_assum irule >> simp[]) >>
  `stmt_state_rel H ctx func ce cx (ee with scopes := []) t` by
    (irule internal_return_exit_stmt_state_rel >> qexists_tac `ce` >>
     fs[expr_post_def, same_frame_def]) >>
  drule_all internal_return_value_compile >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >> simp[]
QED
