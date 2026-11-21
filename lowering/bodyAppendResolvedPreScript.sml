(* Body inputs shared by local, subscript and attribute Append simulations. *)
Theory bodyAppendResolvedPre
Ancestors
  bodyAugPlaceTarget bodySimAugPlaceLoad bodyAppendStorageFacts bodyExprPreFacts bodyStorageCases
  bodySim exprSimHypsDefs targetPlaceSim targetPlaceLive gasContext
  supportedTypes supportedStmts supportedTargets supportedExprs supportedExprTraverse
  supportedStmtTraverse allocLimits allocLimitsProps exprLowering
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperExprEffects vyperAST list popTargetPre vyperTypeEnv vyperTypeInvariants
  compileEnv finite_map

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

Theorem target_widths_indices[local]:
  !bt. byte_widths_target bt <=> EVERY byte_widths_expr (target_indices bt)
Proof
  recInduct targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  simp[byte_widths_expr_def, target_indices_def]
QED

Theorem append_typed_root_not_immutable[local]:
  expr_sim_inv cenv cx env es /\
  type_place_target env bt = SOME ty /\
  ~target_in_immutables cenv.ce_module_vars bt ==>
  ~immutable_root cx bt
Proof
  strip_tac >> simp[immutable_root_def] >> rpt strip_tac >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  `?t. FLOOKUP env.bare_global_assignable (src,id) = SOME t` by
    (Cases_on `type_place_target env (TopLevelNameTarget (src,id))`
     >- (qspecl_then [`env`, `bt`] mp_tac target_root_untyped >> simp[]) >>
     gvs[type_place_target_TopLevelNameTarget] >>
     rename1 `FLOOKUP env.toplevel_vtypes _ = SOME vt` >> Cases_on `vt` >>
     fs[env_context_consistent_def] >> res_tac >> gvs[]) >>
  `FLOOKUP env.bare_globals (src,id) = SOME t` by
    (fs[env_context_consistent_def] >> metis_tac[]) >>
  `?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)` by
    (`IS_SOME (FLOOKUP env.bare_global_assignable (src,id))` by fs[] >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[target_in_immutables_root]
QED

Theorem body_append_typed_pre:
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
  ?elem cap. type_place_target env bt =
    SOME (Type (ArrayT elem (Dynamic cap))) /\
    type_widens_to env.type_defs (expr_type e) elem
Proof
  strip_tac >>
  drule_then strip_assume_tac append_typing_target >>
  `supported_expr tops e` by
    fs[Once supported_stmt_def, supportedExprsTheory.supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  drule_then assume_tac supported_stmt_body_safe >>
  drule_all body_inv_stmt_const_name_free >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
  `~is_extcode e` by
    (irule alloc_limits_expr_not_extcode >> qexists_tac `cenv` >>
     fs[stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
  `cx_tops cx = tops` by metis_tac[gasContextTheory.cx_tops_module] >>
  conj_tac >- suspend "target" >>
  suspend "rhs"
QED

Resume body_append_typed_pre[target]:
  `alloc_limits_target cenv bt /\ ~target_in_immutables cenv.ce_module_vars bt` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  simp[target_pre_def] >>
  conj_tac >- metis_tac[append_typed_root_not_immutable] >>
  `byte_widths_target bt` by
    (drule_then assume_tac alloc_limits_target_indices_not_extcode >>
     simp[target_widths_indices, EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM key (target_indices bt)` >>
     `~is_extcode key` by fs[EVERY_MEM] >>
     CCONTR_TAC >>
     `supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) key` by
       (irule supported_expr_exists_root >> simp[]) >>
     fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
        supported_target_exists_indices, EXISTS_MEM] >> metis_tac[]) >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, EVERY_APPEND, DE_MORGAN_THM]) >>
  irule target_indices_pre_of_body >>
  simp[] >> conj_tac
  >- fs[supported_stmt_expr_exists_def] >>
  fs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_left]
QED

Resume body_append_typed_pre[rhs]:
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Finalise body_append_typed_pre

Theorem body_append_resolved_pre:
  supported_full_word_type (expr_type e) /\
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
  drule_all body_append_typed_pre >> strip_tac >>
  metis_tac[append_full_word_source_rigid]
QED

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
