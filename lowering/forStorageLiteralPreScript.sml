(* Prepare a literal storage iterator's expression endpoint. *)
Theory forStorageLiteralPre
Ancestors
  bodyFullForFacts bodyInvExecutionProps bodySim exprSimHypsDefs gasContext
  allocLimits exprLowering supportedExprTraverse supportedStmtTraverse supportedProgram
  vyperTypeCallGraph vyperTypeSystem

val _ = Parse.hide "body";

Theorem for_storage_literal_expr_pre:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) =
    SOME env' /\
  stmt_exprs_ok cenv (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) /\
  call_evaluation_safe cx
    (int_calls_stmt (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)) ==>
  expr_body_pre cenv cx env (TopLevelName (ArrayT typ bd) nid) es
Proof
  strip_tac >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_then strip_assume_tac body_inv_main_support >>
  drule_then assume_tac cx_tops_module >>
  drule_all_then mp_tac body_inv_stmt_const_name_free >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  qpat_assum `stmt_exprs_ok _ _` mp_tac >>
  simp[NoAsms, stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_iterator_def,
       supported_stmt_expr_exists_def, supported_iterator_exists_def,
       supported_expr_exists_def, is_extcode_def] >> strip_tac >>
  fs[expr_body_pre_def, well_typed_iterator_def, int_calls_expr_def,
     int_calls_stmt_def, int_calls_iterator_def, expr_has_evm_run_thm,
     supported_expr_exists_def, expr_abi_decode_target_root_def] >>
  metis_tac[body_inv_singleton_abi_types,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono,
            listTheory.MEM]
QED
