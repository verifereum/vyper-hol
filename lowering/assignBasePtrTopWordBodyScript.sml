(* Supported scalar module targets are runtime storage/transient slots. *)
Theory assignBasePtrTopWordBody
Ancestors assignBasePtrTopWordFragment assignBasePtrStorageBody
  assignTuplePtrBodyReady bodyPtrPreds bodyPtrDefs bodySim bodyExprPreFacts
  exprSimHypsDefs exprSimHyps exprSimSource exprSimTopLevelProps stmtSimAssignStorage
  compileEnv vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend
  vyperTypeEnv vyperTyping vyperTypeContractStaticMaps supportedDecls
  supportedProgram supportedTypes supportedStmtTraverse supportedExprTraverse
  supportedExprs supportedStmts vyperInterpreter vyperState vyperTypeValues
  valueEncodingProps stmtLowering exprLowering finite_map list
  vyperTypeSystem vyperTypeCallGraph gasContext bodyStorageMetadata
  vyperTypeContract vyperTypeInvariants vyperTypeExprSoundness
Libs monadsyntax

Theorem body_assign_toplevel_word_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) ==>
    occurs_abi_decode_target target tops) /\
  supported_scalar_target tops (src,id) /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  strip_tac >>
  `src = NONE /\ ?mut ty slot.
     supported_variable_decl tops (src,id) = SOME (Private,mut,ty,SOME slot) /\
     (mut = Storage \/ mut = Transient) /\ is_word_type ty` by
    (qpat_x_assum `supported_scalar_target _ _` mp_tac >>
     simp[supported_scalar_target_def] >>
     Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
     rename1 `SOME x` >> PairCases_on `x` >>
     Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >>
     simp[supported_full_word_type_def, is_word_type_def] >>
     rpt strip_tac >> drule supported_variable_decl_mem >> strip_tac >>
     gvs[is_word_type_def]) >>
  drule_at (Pos (el 2)) assign_base_storage_target >>
  disch_then drule >> simp[] >> disch_then drule >>
  disch_then (qspecl_then [`ret_ty`, `env'`, `e`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `expr_type e = ty` by
    (`env_consistent env cx es` by fs[expr_sim_inv_def] >>
     Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
     gvs[type_stmt_def, atarget_accepts_def] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[type_place_target_TopLevelNameTarget]
     >- (drule_all assign_base_bare_assignable_no_decl >> strip_tac >> gvs[]) >>
     drule_all env_consistent_toplevel_storage_static >> strip_tac >>
     drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
     metis_tac[type_widens_to_word]) >>
  drule_all assign_base_storage_rhs_pre >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ptr_ok_def] >>
  irule compile_assign_storage_typed_stmt_frag_ptr >> simp[] >>
  rpt strip_tac >> drule_all expr_body_pre_eval_gas_ptr >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[value_runtime_typed_def]
QED
