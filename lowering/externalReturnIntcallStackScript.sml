Theory externalReturnIntcallStack
Ancestors
  externalReturnIntcallForce stmtSimReturn exprSimDefs exprLowering
  compileEnv loweringPosts gasOutcome gasSummary vyperAST vyperInterpreter
  exprSimMemorySource

Theorem return_stack_lower_value:
  compile_expr ce ct e sa = (StackValue ty op,sm) ==>
  lower_value compile_expr ce ct e sa = (op,sm)
Proof
  simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def]
QED

Theorem return_intcall_stack_force:
  compile_expr ce ct (Call ann (IntCall fid) args drv) sa =
    (StackValue ty (Lit 0w),sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  expr_sim ctx func ce cx ct (Call ann (IntCall fid) args drv) es /\
  gas_admissible
    (eval_stmt cx (Return (SOME (Call ann (IntCall fid) args drv))))
    (stmt_res_ok lctx) es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
    (es,s0)
    (\res ee s. ?v. res = INL v /\
      expr_post ctx func ce cx (Call ann (IntCall fid) args drv)
        es sa sm s0 ee v (Lit 0w) s /\
      s.vs_current_bb = sm.cs_current_bb /\
      s.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule return_stack_lower_value >> strip_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_def] >> disch_then drule_all >> simp[]
QED
