(* Semantic boundaries shared by counted and uncounted mapping subscripts. *)
Theory mappingSubscriptSemantics
Ancestors
  exprSimSubscriptMap exprSimWordArgs exprSimProps loweringPosts freshWrites
  list exprSimMapDefs exprSimSource exprSimHypsDefs exprSimHyps exprSimPop
  exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimDefs gasContext gasSummary gasSummaryCompose
  gasExemptCert vyperState exprLowering placeTypingProps vyperAST
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  supportedExprTraverse allocLimits exprOracleStoragePreservation
  bodyStoragePreservation vyperCallOutcomeStorage vyperEvalOutcomeSuffix
  vyperTypeInvariants vyperTypeEvalSoundness vyperTypeExprResult
  vyperRuntimeAccounts vyperExprNoControl vyperPlaceInvariants
  vyperTypeExprSoundness vyperTypeStoragePreservation exprSimMapKey
  vyperStorageLayoutSafety vyperStorageBackend accountsRelProps
  vyperTypeValues vyperLookupStorage exprSimTopLevelProps compileEnv
  loweringStateRelDefs finite_map fragGasPath fragGasMode vyperInterpreter
  vyperTypeEnv vyperStoragePlaceProvenance exprLoweringProps
  exprSimSubscriptArraySource gasOutcome context venomState

Theorem mapping_subscript_frames:
  wb_frame cenv es em sa s0 t /\ wb_frame cenv em en sm t out /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (~expr_has_effect obj ==> pure_frame cenv func es sa s0 t) /\
  (~expr_has_effect idx ==> pure_frame cenv func em sm t out) ==>
  wb_frame cenv es en sa s0 out /\
  (~expr_has_effect (Subscript ann obj idx) ==>
     pure_frame cenv func es sa s0 out)
Proof
  strip_tac >> conj_tac
  >- (irule wb_frame_trans >> metis_tac[]) >>
  rewrite_tac[expr_has_effect_thm, DE_MORGAN_THM] >> strip_tac >>
  `!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP out.vs_allocas aid = SOME b` by
    (qpat_assum `wb_frame cenv em en sm t out` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w` by
    (qpat_assum `wb_frame cenv es em sa s0 t` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  irule pure_frame_trans >> simp[] >> qexistsl [`em`, `sm`, `t`] >> simp[]
QED

Theorem mapping_subscript_marked_base_preparation:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec memory (ctx,func) (eval_expr cx obj)
    (es,s0) marks (INL (HashMapRef tr base_slot bkt bvt)) mid (OK t) /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) ==>
  bkt = kt /\ bvt = vt /\
  expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
  (?s u. eval_expr cx obj s = (INL (HashMapRef tr base_slot bkt bvt),u)) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
   ?s u. eval_expr cx obj s = (INL (HashMapRef tr base_slot bkt bvt),u)` by
    (drule_all mapping_subscript_marked_index_pre >> simp[]) >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `eval_expr cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (HashMapRef tr base_slot bkt bvt),mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >> simp[]) >>
  `bkt = kt /\ bvt = vt` by
    (drule_at (Pat `eval_expr _ _ _ = _`) expr_map_pre_eval_result >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum (qspec_then `HashMapT kt vt` mp_tac) >>
     simp[eval_result_typed_def]) >>
  drule_all subscript_result_index_admissible >> gvs[] >> metis_tac[]
QED
