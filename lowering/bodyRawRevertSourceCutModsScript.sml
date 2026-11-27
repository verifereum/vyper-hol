(* Typed source cut for the single forced argument of RawRevert. *)
Theory bodyRawRevertSourceCutMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimSource exprSafeOperand
  vyperTypeEvalCaseProofs vyperTypeSystem vyperInterpreter vyperValue vyperState
  vyperAST vyperTypeCallGraph supportedExprTraverse allocLimits list rich_list

Theorem raw_revert_source_bind[local]:
  eval_expr cx (Call NoneT RawRevert [e] NONE) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
                (\data. raise (Error (RevertData data))))
Proof
  rw[FUN_EQ_THM] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_def, ignore_bind_def, return_def, type_check_def, assert_def,
       raise_def] >> rpt (CASE_TAC >> gvs[])
QED

Theorem raw_revert_source_cut_mods:
  expr_body_pre_mods mods cenv cx env (Call ann RawRevert args dflt) es ==>
  ?e cap. args = [e] /\ ann = NoneT /\ dflt = NONE /\
    expr_type e = BaseT (BytesT (Dynamic cap)) /\
    evaluate_type (get_tenv cx) (expr_type e) =
      SOME (BaseTV (BytesT (Dynamic cap))) /\
    expr_body_pre_mods mods cenv cx env e es /\
    eval_expr cx (Call ann RawRevert args dflt) =
      bind (bind (eval_expr cx e) (read_result cx))
        (\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
                  (\data. raise (Error (RevertData data))))
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  rename1 `expr_type e = BaseT (BytesT (Dynamic cap))` >>
  `well_typed_expr env e` by fs[well_typed_expr_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  drule_all well_typed_expr_type_well_formed >>
  simp[well_formed_type_def, evaluate_type_def] >> strip_tac >>
  simp[raw_revert_source_bind, evaluate_type_def] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Call _ RawRevert _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, byte_widths_expr_def, alloc_limits_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm,
       supported_expr_exists_def, supported_exprs_exists_every]
QED
