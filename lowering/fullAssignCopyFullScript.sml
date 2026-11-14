(* Caller-facing assembly of the joint aggregate assignment simulation. *)
Theory fullAssignCopyFull
Ancestors
  fullAssignCopyContinuation fullAssignCopyCompose fullAssignCopyFacts
  bodyFullPreds supportedStmts supportedProgram supportedDecls supportedTypes
  gasShadowCompile gasShadowCompileHelpers gasShadow
  vyperLookupStorage vyperStorageLayoutSafety exprSimHypsDefs loweringStateRelDefs
  bodyExprPreFacts bodySim supportedNames bodyStorageMetadata

Theorem compile_assign_toplevel_copy_full:
  !cx nsid mut ty slot e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
    cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    supported_variable_decl tops nsid = SOME (Private,mut,ty,SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ ~is_word_type ty /\
    (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\ expr_type e = ty ==>
    stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> Cases_on `nsid` >>
  rename1 `supported_variable_decl tops (src,id)` >> strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `body_stmt_safe tops (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)` by
    metis_tac[supported_stmt_body_safe] >>
  `expr_body_pre cenv cx env e es` by
    (irule topcopy_rhs_pre >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_at (Pos (el 2)) body_assign_copy_target_vis >>
  disch_then drule >> simp[] >> disch_then drule >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all topcopy_memory_size >> strip_tac >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  `storage_var_info cx NONE id = SOME (tr,off,tvt)` by simp[storage_var_info_def] >>
  drule_all topcopy_region >> strip_tac >>
  `supported_storage_type tops (expr_type e)` by
    (`supported_program tops` by fs[body_inv_def] >>
     drule supported_variable_decl_mem >> strip_tac >>
     drule_all supported_program_declaration >>
     gvs[supported_declaration_header_def]) >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[assign_base_storage_rhs_lowered_type] >>
  `~is_bytestring_type (expr_type e) /\ ~has_length_word (expr_type e)` by
    metis_tac[assign_base_storage_not_bytestring, topcopy_no_length_word] >>
  suspend "assemble"
QED

Resume compile_assign_toplevel_copy_full[assemble]:
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then irule >> metis_tac[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
    (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e))` by
    (mp_tac (Q.SPEC `T` (GEN_ALL (MATCH_MP gas_shadow_compiles_lower_value
      (cj 1 gas_shadow_compile_expr)))) >> simp[]) >>
  simp[gas_shadow_stmt_def] >>
  irule compile_assign_copy_frag_full >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule topcopy_store_continuation >>
      goal_assum (drule_at Any) >> simp[] >>
      conj_tac
      >- (fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
      metis_tac[topcopy_rhs_value_typed]) >>
  metis_tac[topcopy_rhs_value_typed]
QED

Finalise compile_assign_toplevel_copy_full
