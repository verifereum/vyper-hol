(* Source preservation at the two success cuts of a linked write subscript. *)
Theory bodyWriteSubscriptSourceMods
Ancestors
  bodySimStmtFacts bodyNormalHeadTailMods bodyBranchCellFrameMods
  targetPlaceSimCasesBase constSubstCorrect exprBodyPreProps
  supportedExprs vyperTypeEnv vyperEvalMisc vyperPlaceFrames exprSimHypsDefs
  vyperState vyperInterpreter vyperTypeSystem vyperTypeExprResult list option
Libs
  monadsyntax

Theorem write_subscript_source_gas_obs_mods[simp]:
  (expr_sim_inv_mods mods cenv cx env (st with gas_obs := obs) <=>
   expr_sim_inv_mods mods cenv cx env st) /\
  (expr_body_pre_mods mods cenv cx env e (st with gas_obs := obs) <=>
   expr_body_pre_mods mods cenv cx env e st)
Proof
  simp[expr_body_pre_mods_def, expr_sim_inv_mods_def]
QED

Theorem write_subscript_source_trace_mods[local,simp]:
  (expr_sim_inv_mods mods cenv cx env (st with storage_trace := obs) <=>
   expr_sim_inv_mods mods cenv cx env st) /\
  (body_const_cells_agree_mods mods cx env (st with storage_trace := obs) <=>
   body_const_cells_agree_mods mods cx env st)
Proof
  simp[expr_sim_inv_mods_def] >>
  irule body_const_cells_agree_mods_immutables >> simp[]
QED

Theorem write_index_read_cells_mods[local]:
  well_typed_expr env e /\ body_const_cells_agree_mods mods cx env st /\
  bind (eval_expr cx e) (read_result cx) st = (INL v,mid) ==>
  body_const_cells_agree_mods mods cx env mid
Proof
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  rename1 `eval_expr cx e st = (INL raw,mid)` >>
  `?res. eval_stmt cx (Expr e) st = (res,mid)` by
    (simp[Once evaluate_def, bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef raw` >> simp[]) >>
  `type_stmt env NoneT (Expr e) = SOME env` by
    simp[type_stmt_def, well_typed_expr_not_hashmap_place] >>
  irule body_const_cells_agree_mods_stmt >>
  goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
  qexistsl_tac [`env`,`NoneT`] >> simp[]
QED

Theorem write_index_read_source_mods:
  expr_body_pre_mods mods cenv cx env e st /\
  body_const_cells_agree_mods mods cx env st /\
  bind (eval_expr cx e) (read_result cx) st = (INL v,mid) ==>
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  value_runtime_typed env (expr_type e) v
Proof
  strip_tac >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac write_index_read_cells_mods >> simp[]
QED

Theorem write_base_reached_source_mods:
  !bt mods cenv cx env st pv mid.
    expr_sim_inv_mods mods cenv cx env st /\
    body_const_cells_agree_mods mods cx env st /\
    IS_SOME (type_place_target env bt) /\
    (!i s. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env s ==>
           expr_body_pre_mods mods cenv cx env i s) /\
    eval_base_place cx bt st = (INL pv,mid) ==>
    expr_sim_inv_mods mods cenv cx env mid /\
    body_const_cells_agree_mods mods cx env mid
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> drule eval_base_place_NameTarget_preserves_state >> simp[])
  >- (strip_tac >> drule eval_base_place_TopLevelNameTarget_preserves_state >>
      disch_then (fn th => once_rewrite_tac[th]) >> simp[])
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      drule type_place_target_subscript_child >> strip_tac >>
      qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_apply, AllCaseEqs()] >> strip_tac >>
      gvs[target_indices_def, MEM_APPEND] >>
      rename1 `eval_base_place cx bt st = (INL base_pv,at_base)` >>
      `expr_sim_inv_mods mods cenv cx env at_base /\
       body_const_cells_agree_mods mods cx env at_base` by
        (first_x_assum irule >> reverse (rpt conj_tac)
         >- (qexistsl_tac [`base_pv`,`st`] >> simp[])
         >- simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
      `expr_body_pre_mods mods cenv cx env e at_base` by simp[] >>
      rename1 `read_result cx raw at_raw = (INL v,at_index)` >>
      `bind (eval_expr cx e) (read_result cx) at_base = (INL v,at_index)` by
        simp[bind_def] >>
      drule_all_then strip_assume_tac write_index_read_source_mods >>
      drule extend_place_state >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule type_place_target_attribute_child >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_apply, AllCaseEqs()] >> strip_tac >>
  gvs[target_indices_def] >>
  rename1 `eval_base_place cx bt st = (INL base_pv,at_base)` >>
  drule extend_place_state >> disch_then (fn th => once_rewrite_tac[th]) >> simp[] >>
  first_x_assum irule >> simp[] >> qexistsl_tac [`base_pv`,`st`] >> simp[]
QED
