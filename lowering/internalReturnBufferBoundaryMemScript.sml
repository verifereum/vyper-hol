(* Compilation and source boundary for caller-buffer internal returns. *)
Theory internalReturnBufferBoundaryMem
Ancestors
  internalReturnBufferMem bodyMemoryDefs stmtLowering loweringPosts
  exprLoweringProps compileEnv ctorReturnFrame bodySim loweringStateRelDefs
  vyperState exprSimHypsDefs vyperTypeInvariants vyperTypeEnvPreservation
  returnValueTyped vyperTypeArgFits valueEncodingTyping vyperTypeSystem
  exprSimMemDefs internalReturnBoundaryCommonMem typedMemoryCopy stmtLoweringMono stmtSimReturn
  venomState loweringShapeDefs externalReturnPrefix fragExec externalReturnCopyRecursive
  intCallReturnMem valueCopyBytes

Theorem internal_return_buffer_compile[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_return_buf = SOME (PtrVar (Var bx) sz) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  lower_value compile_expr cenv ty e sa = (op,s1) ==>
  ?su. compile_return_unlock cenv s1 = ((),su) /\
    compile_internal_return cenv (SOME op) (Var rpc) cenv.ce_returns_count
      ty (lowered_value_type cenv e)
      (case ty of TupleT tys => tys
       | StructT nsid => MAP (FST o SND)
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
       | _ => []) (SOME (Var bx)) su = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       compile_internal_return_from_env_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED


Theorem internal_return_source_env[local]:
  expr_sim_inv cenv cx env es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) = (INL v,ee) ==>
  env_consistent env cx ee
Proof
  strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  irule eval_expr_preserves_ec >>
  goal_assum (drule_at Any) >> fs[expr_sim_inv_def]
QED

Theorem internal_return_buffer_immutables[local]:
  bare_globals_layout cenv.ce_is_ctor cenv.ce_module_var_type
    cenv.ce_module_vars cx env.bare_globals env.bare_global_assignable /\
  env_consistent env cx ee /\
  (!nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) (w2n bw) cap) ==>
  !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) cap
Proof
  rw[bare_globals_layout_def, env_consistent_def, env_immutables_consistent_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >> metis_tac[]
QED

Theorem internal_return_buffer_value_types:
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
    value_has_type stv v /\ value_has_type tv v /\ val_wf tv v
Proof
  strip_tac >> drule_all return_value_typed >> strip_tac >>
  `type_widens_to (get_tenv cx) (expr_type e) ty` by
    gvs[type_stmt_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def, AllCaseEqs()] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  gvs[] >> metis_tac[value_has_type_val_wf]
QED

Theorem internal_return_buffer_source_window[local]:
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  lowered_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  ~is_word_type (expr_type e) /\ expr_store_bound cx (expr_type e) v op s ==>
  ?sw. eval_operand op s = SOME sw /\
    (val_store_size stv v = 0 \/
     w2n sw + val_store_size stv v <= s.vs_alloca_next)
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_lowered] >>
  fs[expr_post_def, expr_val_at_def, expr_store_bound_def] >> metis_tac[]
QED
Theorem internal_return_buffer_frame[local]:
  return_buf_frame (SOME (bw,cap)) ce s1 t ==>
  ?bx sz. ce.ce_return_buf = SOME (PtrVar (Var bx) sz) /\
    eval_operand (Var bx) t = SOME bw /\ not_fresh_at s1 bx /\
    w2n bw + cap <= t.vs_alloca_next
Proof
  simp[return_buf_frame_def, eval_operand_def] >> metis_tac[]
QED

Theorem internal_return_buffer_code[local]:
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_return_buf = SOME (PtrVar (Var bx) sz) /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr ce ty e sa = (op,s1) /\
  fn_has_code s1 sb func ==>
  ?su. compile_return_unlock ce s1 = ((),su) /\
    compile_internal_return ce (SOME op) (Var rpc) ce.ce_returns_count
      ty (lowered_value_type ce e)
      (case ty of TupleT tys => tys | StructT nsid => MAP (FST o SND)
        (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) | _ => [])
      (SOME (Var bx)) su = ((),sb) /\
    fn_has_code s1 su func /\ fn_has_code su sb func
Proof
  strip_tac >> drule_all internal_return_buffer_compile >> strip_tac >>
  `cs_extends s1 su` by metis_tac[compile_return_unlock_shape] >>
  `cs_extends su sb` by
    metis_tac[cj 1 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  metis_tac[fn_has_code_split]
QED


Theorem internal_return_buffer_boundary_mem:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_imm_alloca = NONE /\ cenv.ce_returns_count = 0 /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (expr_type e = ty \/ is_bytestring_type ty) /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (cenv.ce_is_ctor ==> !nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  lowered_value_type ce e = expr_type e /\
  stmt_env ce lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
  lower_value compile_expr ce ty e sa = (op,s1) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\ ret_pc_ok ce sa s0 /\
  return_buf_frame (SOME (bw,type_memory_size tv)) ce s1 t /\
  expr_post ctx func ce cx e es sa s1 s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v, ee with gas_obs := [])) /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  ?n r. gas_path_mem ctx func t n r /\
    intret_mem_q func cenv cx tv bw v (ee with scopes := []) r
Proof
  strip_tac >>
  `env_consistent env cx ee` by
    (drule_all internal_return_source_env >> simp[]) >>
  drule_all internal_return_buffer_value_types >> strip_tac >>
  `type_widens_to (get_tenv cx) (expr_type e) ty` by
    gvs[type_stmt_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def, AllCaseEqs()] >>
  `ce.ce_return_pc = cenv.ce_return_pc /\ ce.ce_imm_alloca = NONE /\
   ce.ce_returns_count = 0` by
    fs[same_frame_def, compile_env_component_equality] >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) internal_return_value_preparation >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule internal_return_buffer_frame >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) internal_return_buffer_code >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `~is_word_type (expr_type e) /\
   (expr_type e = ty \/ is_bytestring_type (expr_type e) /\ is_bytestring_type ty)` by
    metis_tac[typed_copy_bytestring_source, is_bytestring_word_type] >>
  drule_all internal_return_buffer_source_window >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (irule return_copy_memory_size >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (rpt strip_tac >> irule internal_return_buffer_immutables >>
     qexistsl_tac [`ce`,`cx`,`ee`,`env`] >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
     gvs[expr_sim_inv_def, same_frame_def, compile_env_component_equality] >>
     metis_tac[]) >>
  `expr_val_rel cx (expr_type e) v op t` by
    (fs[expr_post_def, expr_val_at_def] >> metis_tac[post_value_type_lowered]) >>
  `?n r. gas_path_mem ctx func t n r /\
     intret_mem_q func ce cx tv bw v (ee with scopes := []) r` by
    (irule compile_internal_return_buffer_path_mem >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `compile_return_unlock _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
     gvs[] >> metis_tac[]) >>
  goal_assum (drule_at Any) >>
  fs[intret_mem_q_def] >> metis_tac[internal_return_post_frame]
QED
