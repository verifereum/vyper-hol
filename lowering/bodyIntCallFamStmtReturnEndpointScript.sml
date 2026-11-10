(* Count-independent terminal boundary for a forced return value. *)
Theory bodyIntCallFamStmtReturnEndpoint
Ancestors
  bodyIntCallFamStmtReturnStackEndpoint bodyIntCallFamStmtReturnMemoryEndpoint
  bodyIntCallFamStmtReturnEndpointTypes bodyIntCallJointContract
  exprSimHypsDefs exprSimDefs exprSimHyps loweringPosts compileEnv bodySim
  exprSimSource vyperTypeInvariants

Theorem intcall_return_endpoint:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sm t /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\
  type_widens_to env.type_defs (expr_type e) fp.jc_ret_ty /\
  fp.jc_ret_ty <> NoneT /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ value_has_type fp.jc_ret_tv v /\
  expr_val_rel fp.jc_cx (post_value_type ce e) v op t /\
  expr_val_at ce fp.jc_cx (post_value_type ce e) sa sm ee v op t /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) ==>
   !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv' ==>
    ?w a k. eval_operand op t = SOME w /\ a <= w2n w /\
     w2n w + type_memory_size tv' <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  compile_internal_return_from_env ce fp.jc_ret_ty (lowered_value_type ce e)
    op fp.jc_rpc sm = ((),sb) /\
  fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?k r. gas_path fp.jc_ctx fp.jc_func t k r /\ exit_result r /\
    intcall_stmt_exit fp (INR (ReturnException v)) ee r
Proof
  strip_tac >> Cases_on `fp.jc_root_ce.ce_returns_count = 0`
  >- (irule intcall_memory_return_endpoint >> metis_tac[]) >>
  `0 < fp.jc_root_ce.ce_returns_count` by decide_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  `0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields fp.jc_root_ce.ce_struct_fields name))
    fp.jc_ret_ty` by fs[intcall_frame_ok_def] >>
  drule_all return_stack_post_type >> strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx)` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule intcall_stack_return_endpoint >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
