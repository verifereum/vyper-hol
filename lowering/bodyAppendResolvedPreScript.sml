(* Body inputs shared by local, subscript and attribute Append simulations. *)
Theory bodyAppendResolvedPre
Ancestors
  bodyAugPlaceTarget bodySimAugPlaceLoad bodyAppendStorageFacts bodyExprPreFacts bodyStorageCases
  bodySim exprSimHypsDefs targetPlaceSim targetPlaceLive gasContext
  supportedTypes supportedStmts supportedTargets supportedExprs supportedExprTraverse
  supportedStmtTraverse allocLimits allocLimitsProps exprLowering
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperExprEffects vyperAST list

Theorem append_full_word_source_rigid[local]:
  !tenv t u.
    supported_full_word_type t /\ type_widens_to tenv t u ==> u = t
Proof
  rw[supported_full_word_type_def, type_widens_to_def] >>
  Cases_on `u` >> gvs[arg_type_fits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[arg_type_fits_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> gvs[arg_type_fits_def]
QED

Theorem append_target_indices_pure:
  !bt. ~supported_target_exists (\e. ~pure_expr e) bt ==>
    EVERY pure_expr (target_indices bt)
Proof
  `(!e:expr. T) /\
   !bt. ~supported_target_exists (\e. ~pure_expr e) bt ==>
     EVERY pure_expr (target_indices bt)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[supported_expr_exists_def, target_indices_def, EVERY_APPEND] >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `supported_expr_exists (\e. ~pure_expr e) e` by
    (irule supported_expr_exists_root >> simp[]) >> gvs[]
QED

Theorem body_append_resolved_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Append bt e) /\
  ~(?id. bt = TopLevelNameTarget id) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Append bt e) = SOME env' /\
  stmt_exprs_ok cenv (Append bt e) /\
  call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Append bt e) ==> occurs_abi_decode_target target tops) ==>
  target_pre cenv cx env bt es /\ expr_body_pre cenv cx env e es /\
  ?cap. type_place_target env bt =
    SOME (Type (ArrayT (expr_type e) (Dynamic cap)))
Proof
  strip_tac >>
  `supported_full_word_type (expr_type e) /\
   IS_SOME (supported_target_info tops bindings bt) /\
   supported_pure_expr tops e` by
    (Cases_on `bt` >> gvs[Once supported_stmt_def]) >>
  drule append_typing_target >> strip_tac >>
  `elem = expr_type e` by metis_tac[append_full_word_source_rigid] >>
  qpat_x_assum `elem = expr_type e` SUBST_ALL_TAC >>
  `body_stmt_safe tops (Append bt e)` by metis_tac[supported_stmt_body_safe] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  conj_tac >- suspend "target" >>
  conj_tac >- suspend "rhs" >> metis_tac[]
QED

Resume body_append_resolved_pre[target]:
  simp[target_pre_def] >> conj_tac
  >- metis_tac[aug_place_supported_root_not_immutable, optionTheory.IS_SOME_EXISTS] >>
  `alloc_limits_target cenv bt` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. ~is_extcode e) (target_indices bt)` by
    metis_tac[alloc_limits_target_indices_not_extcode] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, EVERY_APPEND, DE_MORGAN_THM]) >>
  irule aug_place_target_indices_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      alloc_limits_stmt_def, int_calls_stmt_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Resume body_append_resolved_pre[rhs]:
  `supported_expr tops e` by metis_tac[supported_expr_def] >>
  drule supported_expr_body_calls >> strip_tac >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Finalise body_append_resolved_pre

Theorem append_resolved_rhs_body_pre:
  expr_body_pre cenv cx env e es /\ target_pre cenv cx env bt es /\
  eval_target_place cx bt es = (INL p,ee) ==>
  expr_body_pre cenv cx env e ee
Proof
  rpt strip_tac >>
  `expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt` by
    fs[expr_body_pre_def, target_pre_def] >>
  drule_all aug_place_target_inv >>
  fs[expr_body_pre_def]
QED
