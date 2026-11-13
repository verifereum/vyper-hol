(* Source boundary for primitive internal stack returns. *)
Theory internalReturnWordBoundaryMem
Ancestors
  internalReturnStackMem internalReturnBufferBoundaryMem externalReturnPrefix
  stmtLowering loweringPosts compileEnv exprSimHypsDefs vyperTypeSystem
  stmtSimProps bodySim ctorReturnFrame vyperTypeInvariants exprLoweringProps
  fragExec venomExecSemantics loweringStateRelDefs stmtSimReturn stmtSimDefs
  stmtLoweringMono venomState internalReturnBoundaryCommonMem


Theorem internal_return_word_count[local]:
  is_word_type ty ==> returns_stack_count sft ty = 1
Proof
  Cases_on `ty` >> simp[is_word_type_def, returns_stack_count_def]
QED

Theorem internal_return_word_boundary_mem:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count =
    returns_stack_count
      (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name)) ty /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  lowered_value_type ce e = expr_type e /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr ce ty e sa = (op,s1) /\
  fn_has_code sa sb func /\ ret_pc_ok ce sa s0 /\
  return_buf_frame NONE ce sa s0 /\
  expr_post ctx func ce cx e es sa s1 s0 ee v op t /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  ?n r. gas_path_mem ctx func t n r /\
    intret_q func cenv cx tv v (ee with scopes := []) r
Proof
  strip_tac >>
  `expr_type e = ty` by
    (irule type_widens_to_word >> simp[] >> qexists_tac `get_tenv cx` >>
     gvs[type_stmt_def, expr_sim_inv_def, env_consistent_def,
         env_context_consistent_def, AllCaseEqs()]) >>
  `post_value_type ce e = ty` by metis_tac[post_value_type_lowered] >>
  `ce.ce_return_pc = cenv.ce_return_pc /\
   ce.ce_returns_count = cenv.ce_returns_count /\
   ce.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  `ce.ce_returns_count = 1` by metis_tac[internal_return_word_count] >>
  `compile_internal_return_from_env ce ty (lowered_value_type ce e)
     op (Var rpc) s1 = ((),sb)` by metis_tac[internal_return_value_compile] >>
  `cs_extends sa s1` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `cs_extends s1 sb` by metis_tac[return_value_code_prefix] >>
  `fn_has_code s1 sb func` by metis_tac[fn_has_code_split] >>
  `?pc. eval_operand (Var rpc) t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def, eval_operand_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes := []) t` by
    (irule internal_return_exit_stmt_state_rel >> qexists_tac `ce` >>
     fs[expr_post_def]) >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  `~t.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `ce.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
  drule_all compile_internal_word_return_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[intret_q_def] >>
  qexistsl_tac [`t`, `(return_unlock_state cenv t).vs_inst_idx`] >>
  simp[result_rel_def, return_unlock_state_def] >>
  conj_tac >- fs[stmt_state_rel_def] >>
  metis_tac[intret_vals_match_word]
QED
