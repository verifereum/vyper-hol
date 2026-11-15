(* Memory return endpoint with the executed optional release. *)
Theory bodyIntCallMemoryUnlockEndpoint
Ancestors
  bodyIntCallMemoryStoreEffect bodyIntCallReturnUnlockMemory
  externalReturnSelectedSuffix stmtSimReturn bodySim stmtLowering
  exprLoweringProps compileEnv loweringPosts emitHelperProps venomState
  bodyIntCallJointContract loweringStateRelDefs fragExec

Theorem intcall_memory_return_unlock_endpoint:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es0 /\
  type_widens_to env.type_defs (expr_type e) fp.jc_ret_ty /\
  fp.jc_root_ce.ce_returns_count = 0 /\ fp.jc_ret_ty <> NoneT /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ value_has_type fp.jc_ret_tv v /\
  expr_val_rel fp.jc_cx (post_value_type ce e) v op s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) ==>
   ?w a k. eval_operand op s = SOME w /\ a <= w2n w /\
     w2n w + type_memory_size tv <= a + k /\ a + k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  compile_internal_return_from_env ce fp.jc_ret_ty (lowered_value_type ce e)
    op fp.jc_rpc sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?k r. gas_path fp.jc_ctx fp.jc_func s k r /\ exit_result r /\
    intcall_stmt_exit fp (INR (ReturnException v)) es r
Proof
  strip_tac >>
  `?bw cap. fp.jc_rb = SOME (bw,cap)` by
    (fs[intcall_frame_ok_def] >> Cases_on `fp.jc_rb` >> gvs[] >>
     rename1 `fp.jc_rb = SOME bc` >> Cases_on `bc` >> simp[]) >>
  `ce.ce_returns_count = 0 /\
   returns_stack_count
     (\name. MAP (FST o SND) (get_struct_fields fp.jc_root_ce.ce_struct_fields name))
     fp.jc_ret_ty = 0` by
    fs[intcall_joint_res_def, intcall_expr_res_def, intcall_frame_ok_def,
       same_frame_def, compile_env_component_equality] >>
  `~is_word_type fp.jc_ret_ty` by
    (Cases_on `fp.jc_ret_ty` >> gvs[returns_stack_count_def, is_word_type_def] >>
     rename1 `is_word_type (BaseT bt)` >>
     Cases_on `is_word_type (BaseT bt)` >> gvs[]) >>
  `?x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) /\
    eval_operand (Var x) s = SOME bw /\ not_fresh_at sa x` by
    fs[intcall_joint_res_def, intcall_expr_res_def, return_buf_frame_def, eval_operand_def] >>
  `~s.vs_call_ctx.cc_static` by
    fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_return_unlock ce sa = (unit,su)` >> Cases_on `unit` >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory _ _ _ _ _ su = (unit,sm)` >> Cases_on `unit` >>
  `ci_mono sa su /\ ci_mono su sm /\ ci_mono sm sb` by
    (mp_tac ci_mono_compile_store_memory >> mp_tac ci_mono_emit_inst >>
     mp_tac stmtLoweringMonoTheory.ci_mono_compile_return_unlock >> metis_tac[pairTheory.SND]) >>
  `fn_has_code sa su fp.jc_func /\ fn_has_code su sm fp.jc_func /\
   fn_has_code sm sb fp.jc_func` by
    (`cs_extends su sb` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     `fn_has_code sa su fp.jc_func /\ fn_has_code su sb fp.jc_func` by
       (irule fn_has_code_split >> fs[ci_mono_def] >> goal_assum (drule_at Any)) >>
     drule_at (Pat `fn_has_code _ _ _`) fn_has_code_split >>
     disch_then (qspec_then `sm` mp_tac) >> fs[ci_mono_def]) >>
  ho_match_mp_tac (GEN_ALL return_normalizing_prefix_path) >>
  qexistsl_tac [`su`, `sa`, `\u. u = return_unlock_state ce s`] >>
  simp[] >> conj_tac
  >- (irule compile_return_unlock_frag >> simp[]) >>
  rpt strip_tac >>
  `?t. val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func su sm (return_unlock_state ce s) t (w2n bw) cap` by
    (irule intcall_memory_store_effect >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
     simp[eval_operand_return_unlock] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule intcall_memory_unlock_effect_exit >> simp[] >>
  goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >> metis_tac[]
QED
