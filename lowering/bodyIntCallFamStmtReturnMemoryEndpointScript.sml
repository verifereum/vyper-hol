(* Memory-mode terminal boundary for a forced return value. *)
Theory bodyIntCallFamStmtReturnMemoryEndpoint
Ancestors
  bodyIntCallFamStmtReturnMemorySuffix bodyIntCallFamStmtReturnTypes
  bodyIntCallFamStmtReturnEndpointTypes bodyIntCallJointStmtBoundary
  bodyIntCallJointContract exprSimHyps exprSimHypsDefs exprSimDefs
  loweringPosts stmtLowering exprLoweringProps compileEnv typedMemoryCopy
  vyperTypeInvariants valueEncodingTyping fragExec exprSimSource

Theorem return_post_equal_headroom:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  post_value_type ce e = dty /\ ~is_word_type dty /\
  evaluate_type (get_tenv cx) dty = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\ alloc_limits_expr ce e /\
   well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule_all post_value_type_widens >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule alloc_limits_expr_type_alloc_ok >> strip_tac >>
  irule intcall_widening_sandwich_headroom >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem intcall_memory_store_endpoint:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es0 /\
  type_widens_to env.type_defs (expr_type e) fp.jc_ret_ty /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  fp.jc_ret_ty <> NoneT /\ ~is_word_type fp.jc_ret_ty /\
  evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ value_has_type fp.jc_ret_tv v /\
  expr_val_rel fp.jc_cx (post_value_type ce e) v op s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME bw /\
  (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) ==>
   ?w a k. eval_operand op s = SOME w /\ a <= w2n w /\
     w2n w + type_memory_size tv <= a + k /\ a + k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
  compile_store_memory ce op dst fp.jc_ret_ty (lowered_value_type ce e) sa = ((),sm) /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  emit_inst RET [fp.jc_rpc] [] sm = ((),sb) /\ fn_has_code sm sb fp.jc_func ==>
  ?k r. gas_path fp.jc_ctx fp.jc_func s k r /\ exit_result r /\
    intcall_stmt_exit fp (INR (ReturnException v)) es r
Proof
  strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es0 /\ well_typed_expr env e /\
   alloc_limits_expr ce e` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule_all return_post_type_widens >> strip_tac >>
  `~is_word_type (post_value_type ce e)` by metis_tac[type_widens_from_word] >>
  `?sw. eval_operand op s = SOME sw /\
     val_in_memory tv v (w2n sw) s.vs_memory` by fs[expr_val_rel_def] >>
  Cases_on `is_bytestring_type fp.jc_ret_ty`
  >- (`is_bytestring_type (expr_type e)` by
        metis_tac[typed_copy_bytestring_source] >>
      `post_value_type ce e = expr_type e` by simp[] >>
      `is_bytestring_type (post_value_type ce e)` by simp[] >>
      `type_alloc_ok ce (post_value_type ce e)` by
        metis_tac[alloc_limits_expr_type_alloc_ok] >>
      drule_all intcall_type_alloc_headroom >> strip_tac >>
      drule_all expr_sim_inv_memory_size >> strip_tac >>
      drule_all intcall_bytestring_store_return_exit >> strip_tac >>
      qexists_tac `0` >> goal_assum (drule_at Any) >> simp[exit_result_def]) >>
  `post_value_type ce e <> NoneT /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_NoneT,
              type_widens_from_bytestring] >>
  qpat_x_assum `post_value_type ce e <> NoneT /\ _ ==> _` mp_tac >>
  simp[] >> strip_tac >> gvs[] >>
  `regions_disjoint (w2n sw) (type_memory_size tv) (w2n bw) cap` by
    (irule intcall_return_buffer_source_disjoint >>
     goal_assum (drule_at Any) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `w2n sw + type_memory_size tv < dimword (:256)` by decide_tac >>
  `post_value_type ce e = fp.jc_ret_ty ==>
   type_memory_size fp.jc_ret_tv + 64 < dimword (:256)` by
    (strip_tac >>
     `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv` by
       fs[intcall_frame_ok_def] >>
     irule return_post_equal_headroom >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  drule_all intcall_copy_metadata >> strip_tac >>
  `(!id t. FLOOKUP env.var_types id = SOME t ==>
      well_formed_type env.type_defs t) /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `type_widens_to env.type_defs (expr_type e) fp.jc_ret_ty` by metis_tac[] >>
  drule_all return_store_post_type >> strip_tac >>
  `compile_store_memory ce op dst fp.jc_ret_ty (post_value_type ce e) sa = ((),sm)` by
    metis_tac[] >>
  `val_wf tv v /\ val_wf fp.jc_ret_tv v` by
    metis_tac[value_has_type_val_wf] >>
  drule_all intcall_compound_store_return_exit >> strip_tac >>
  qexists_tac `0` >> goal_assum (drule_at Any) >> simp[exit_result_def]
QED

Theorem intcall_memory_return_endpoint:
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
    fs[intcall_joint_res_def, intcall_frame_ok_def,
       bodySimTheory.same_frame_def, compile_env_component_equality] >>
  `~is_word_type fp.jc_ret_ty` by
    (Cases_on `fp.jc_ret_ty` >>
     gvs[returns_stack_count_def, is_word_type_def] >>
     rename1 `is_word_type (BaseT bt)` >>
     Cases_on `is_word_type (BaseT bt)` >> gvs[]) >>
  `?x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) /\
    eval_operand (Var x) s = SOME bw /\ not_fresh_at sa x` by
    fs[intcall_joint_res_def, return_buf_frame_def, venomStateTheory.eval_operand_def] >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  Cases_on `compile_store_memory ce op (Var x) fp.jc_ret_ty
    (lowered_value_type ce e) sa` >>
  rename1 `_ = (unit,sm)` >> Cases_on `unit` >> simp[] >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (mp_tac ci_mono_compile_store_memory >> mp_tac ci_mono_emit_inst >>
     metis_tac[pairTheory.SND]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> goal_assum (drule_at Any)) >>
  irule intcall_memory_store_endpoint >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >> simp[] >>
  qexists_tac `es0` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
