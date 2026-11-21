(* Prepare a literal storage iterator's expression endpoint. *)
Theory forStorageLiteralPre
Ancestors
  bodyExprPreFacts bodyInvCodeProps bodyInvMetadataProps stmtExprAllocationPreProps
  bodyFullForFacts bodyInvExecutionProps bodySim exprSimHypsDefs gasContext
  allocLimits exprLowering supportedExprTraverse supportedStmtTraverse supportedProgram
  vyperTypeCallGraph vyperTypeSystem

val _ = Parse.hide "body";

Theorem for_storage_literal_expr_pre_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) =
    SOME env' /\
  stmt_exprs_ok cenv (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env)
    (TopLevelName (ArrayT typ bd) nid) /\
  call_evaluation_safe cx
    (int_calls_stmt (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)) ==>
  expr_body_pre_mods mods cenv cx env (TopLevelName (ArrayT typ bd) nid) es
Proof
  strip_tac >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o SIMP_RULE std_ss
    [stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_iterator_def,
     supported_stmt_expr_exists_def, supported_iterator_exists_def, DE_MORGAN_THM]) >>
  qspecl_then [`mods`,`cenv`,`cx`,`env`,`TopLevelName (ArrayT typ bd) nid`,
               `es`,`int_calls_stmts body`] mp_tac stmt_expr_body_pre_mods >>
  gvs[well_typed_iterator_def, int_calls_expr_def, int_calls_stmt_def,
     int_calls_iterator_def, expr_has_evm_run_thm, supported_expr_exists_def,
     expr_abi_decode_target_root_def, is_extcode_def, LEFT_AND_OVER_OR]
QED

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
  mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `cenv` |-> `cenv`,
                   `e` |-> `TopLevelName (ArrayT typ bd) nid`,
                   `s` |-> `For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body`]
            body_inv_stmt_expr_pre_singleton) >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >>
  disch_then irule >> simp[] >>
  strip_tac >> drule_all_then ACCEPT_TAC for_storage_literal_expr_pre_mods
QED
