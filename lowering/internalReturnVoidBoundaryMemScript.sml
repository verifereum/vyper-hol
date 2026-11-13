(* Source and compilation boundary for bare internal returns. *)
Theory internalReturnVoidBoundaryMem
Ancestors
  internalReturnVoidMem ctorReturnFrame bodyMemoryDefs vyperTypeSystem
  vyperTyping stmtLowering loweringPosts bodySim compileEnv stmtSimReturn
  stmtSimDefs exprLoweringProps loweringStateRelDefs venomExecSemantics venomState

Theorem internal_return_void_boundary_mem:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count =
    returns_stack_count
      (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
      ret_ty /\
  IS_SOME (type_stmt env ret_ty (Return NONE)) /\
  same_frame cenv cenv' /\
  stmt_env cenv' lctx ret_ty (Return NONE) sa = (cenv'',sb) /\
  fn_has_code sa sb func /\ ret_pc_ok cenv' sa s0 /\
  stmt_state_rel ctx func cenv' cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path_mem ctx func s0 n r /\
    intret_q func cenv cx ret_tv NoneV (es with scopes := []) r
Proof
  strip_tac >>
  `ret_ty = NoneT` by (gvs[type_stmt_def, AllCaseEqs()]) >>
  `cenv'.ce_return_pc = cenv.ce_return_pc /\
   cenv'.ce_nonreentrant = cenv.ce_nonreentrant` by
    gvs[same_frame_def, compile_env_component_equality] >>
  `compile_stmt cenv' lctx ret_ty (Return NONE) sa = ((),sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     Cases_on `compile_stmt cenv' lctx ret_ty (Return NONE) sa` >>
     gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def]) >>
  `?pc. eval_operand (Var rpc) s0 = SOME pc` by
    gvs[ret_pc_ok_def, eval_operand_def] >>
  `~s0.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  gvs[] >> drule_all compile_internal_void_return_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[intret_q_def] >>
  qexistsl_tac [`s0`, `(return_unlock_state cenv s0).vs_inst_idx`] >>
  simp[result_rel_def, intret_vals_match_def] >>
  conj_tac
  >- simp[return_unlock_state_def] >>
  simp[returns_stack_count_def] >>
  irule constructor_exit_state_rel >>
  qexists_tac `cenv'` >> fs[stmt_state_rel_def]
QED
