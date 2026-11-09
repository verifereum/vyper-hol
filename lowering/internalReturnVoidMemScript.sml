(* A void internal Return executes only its reserved return-PC jump. *)
Theory internalReturnVoidMem
Ancestors
  internalReturnComposeMem internalReturnPathMem ctorReturnFrame
  bodySim stmtSimReturn stmtSimDefs stmtLowering compileEnv loweringPosts
  venomExecSemantics venomState emitHelper fragExec exprSimDefs exprLoweringProps

Theorem internal_return_void_mem:
  same_frame cenv cenv' /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) ==>
  stmt_frag_mem NONE ctx func cx lctx (intret_q func cenv cx ret_tv) cenv'
    (stmt_env cenv' lctx ret_ty (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >> irule internal_return_none_counted_mem >> rpt strip_tac >>
  `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) rsz)` by
    fs[same_frame_def, compile_env_component_equality] >>
  `emit_inst RET [Var rpc] [] sa = ((),sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY,
          compile_stmt_def] >>
     Cases_on `emit_inst RET [Var rpc] [] sa` >> simp[oneTheory.one]) >>
  `?pc. lookup_var rpc s0 = SOME pc` by fs[ret_pc_ok_def] >>
  `gas_path_mem ctx func s0 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s0)` by
    (irule emit_internal_ret_path_mem >> simp[] >>
     qexistsl_tac [`[]`,`pc`,`rpc`,`sa`,`sb`] >> simp[eval_operands_def]) >>
  qexistsl_tac [`0`, `IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s0`] >>
  simp[exit_result_def] >>
  `state_rel func cenv cx (es with scopes := []) s0` by
    (irule constructor_exit_state_rel >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  simp[intret_q_def, result_rel_def, intret_vals_match_def] >> gen_tac >>
  `es with <|scopes := []; gas_obs := tail|> =
    (es with scopes := []) with gas_obs := tail` by simp[] >>
  pop_assum SUBST1_TAC >> simp[state_rel_gas_obs]
QED
