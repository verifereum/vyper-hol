(* Compilation and source boundary for caller-buffer internal returns. *)
Theory internalReturnBufferBoundaryMem
Ancestors
  internalReturnBufferMem bodyMemoryDefs stmtLowering loweringPosts
  exprLoweringProps compileEnv ctorReturnFrame bodySim loweringStateRelDefs
  vyperState exprSimHypsDefs vyperTypeInvariants vyperTypeEnvPreservation
  returnValueTyped vyperTypeArgFits valueEncodingTyping vyperTypeSystem
  exprSimMemDefs

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

Theorem internal_return_exit_stmt_state_rel:
  same_frame cenv cenv' /\ stmt_state_rel ctx func cenv' cx es s ==>
  stmt_state_rel ctx func cenv cx (es with scopes := []) s
Proof
  strip_tac >>
  `state_rel func cenv cx (es with scopes := []) s` by
    (irule constructor_exit_state_rel >> qexists_tac `cenv'` >>
     fs[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_def,
     immutable_base_zero_def, same_frame_def, compile_env_component_equality,
     lookup_scopes_def, local_region_def] >> metis_tac[]
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

Theorem internal_return_buffer_value_types[local]:
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
