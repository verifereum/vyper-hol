(* Semantic boundaries shared by counted and uncounted mapping subscripts. *)
Theory mappingSubscriptSemantics
Ancestors
  exprSimWordArgs exprSimProps loweringPosts freshWrites
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

Theorem subscript_result_index_admissible:
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  gas_marked_exec memory (ctx, func) (eval_expr cx obj)
    (es, s0) marks (INL tv) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx idx) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `expr_map_res_ok (INR ex : eval_result + exception)` suffices_by
    simp[expr_map_res_ok_def, expr_res_ok_def] >>
  first_x_assum irule >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  rewrite_tac[eval_expr_subscript_bind] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  gvs[bind_def]
QED

Theorem expr_map_pre_subscript_base:
  !cenv cx env ann obj idx es.
    expr_map_pre cenv cx env (Subscript ann obj idx) es ==>
    expr_map_pre cenv cx env obj es
Proof
  rpt gen_tac >> strip_tac >>
  `?kt vt. type_place_expr env obj = SOME (HashMapT kt vt)` by
    (fs[expr_map_pre_def, well_typed_expr_def, AllCaseEqs()] >>
     rename1 `subscript_vtype bty _ = SOME (HashMapT _ _)` >>
     Cases_on `bty`
     >- (rename1 `subscript_vtype (Type ty) _ = _` >>
         Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()]) >>
     gvs[subscript_vtype_def, AllCaseEqs()]) >>
  gvs[expr_map_pre_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND,
      Once supported_expr_exists_def] >>
  conj_tac >- metis_tac[call_evaluation_safe_append_left] >>
  rpt strip_tac >>
  qpat_x_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _` irule >>
  simp[Once supported_expr_exists_def]
QED

Theorem expr_subscript_pre_index:
  !cenv cx env ann obj idx es es'.
    (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
     expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
    expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env idx es'
Proof
  rpt gen_tac >>
  simp[expr_body_pre_def, expr_map_pre_def, well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, EVERY_APPEND, supported_expr_exists_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), supported_expr_exists_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem expr_body_pre_map_subscript_base:
  !cenv cx env ann obj idx kt vt es.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = MapPT kt vt ==>
    expr_map_pre cenv cx env obj es
Proof
  rpt gen_tac >> strip_tac >>
  `place_map_tables_agree_on_defined cenv env /\
   (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
              cenv.ce_hashmap_info nsid = NONE)` by
    gvs[expr_body_pre_def, expr_sim_inv_def] >>
  gvs[expr_body_pre_def, Once well_typed_expr_def,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      expr_has_evm_run_thm, EVERY_APPEND]
  >- (drule_all place_type_well_typed_on_defined >> simp[]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  rename1 `type_place_expr env obj = SOME bty` >>
  Cases_on `bty` >> gvs[value_type_place_def] >>
  simp[expr_map_pre_def] >>
  gvs[supported_expr_exists_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

(* Storage preservation accepts both value and place typing. *)
Theorem expr_pre_storage_preserved:
  !cenv cx env e es res es'.
    expr_sim_inv cenv cx env es /\
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    call_evaluation_safe cx (int_calls_expr e) /\ ~expr_has_evm_run e /\
    EVERY (\c. FST c = NONE /\
               ?tops. supported_program tops /\
                      get_module_code cx NONE = SOME tops) (int_calls_expr e) /\
    eval_expr cx e es = (res, es') ==>
    contract_storage_well_formed cx es' /\ oracle_storage_ok cx es'
Proof
  rpt gen_tac >> strip_tac >> (conj_tac
  >- (Cases_on `int_calls_expr e = []`
      >- (drule_at (Pat `eval_expr _ _ _ = _`)
            (cj 5 eval_expr_oracle_storage_mutual) >>
          disch_then (qspec_then `env` mp_tac) >>
          (impl_tac >-
            gvs[expr_sim_inv_def, expr_has_evm_run_def,
                runtime_storage_consistent_def, runtime_consistent_def]) >>
          metis_tac[]) >>
      `?tops. supported_program tops /\ get_module_code cx NONE = SOME tops`
        by (Cases_on `int_calls_expr e` >> gvs[] >> metis_tac[]) >>
      drule_at (Pat `eval_expr _ _ _ = _`) (cj 5 body_oracle_storage_mutual) >>
      disch_then (qspecl_then [`tops`, `env`] mp_tac) >>
      (impl_tac >-
        (gvs[expr_sim_inv_def, listTheory.EVERY_CONJ,
             runtime_storage_consistent_def, runtime_consistent_def] >>
         metis_tac[])) >> metis_tac[]) >>
  irule oracle_storage_ok_suffix >> qexists_tac `es` >>
  gvs[expr_sim_inv_def] >>
  drule_then irule (cj 5 eval_outcome_suffix_mutual))
QED

Theorem expr_map_pre_eval_result:
  !cenv cx env e es res es'.
    expr_map_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !vt tv. type_place_expr env e = SOME vt /\ res = INL tv ==>
            eval_result_typed (env,cx,es') tv vt
Proof
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed cx es' /\ oracle_storage_ok cx es'` by
    (irule expr_pre_storage_preserved >>
     qexistsl_tac [`cenv`, `e`, `env`, `es`, `res`] >>
     gvs[expr_map_pre_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `IS_SOME es'.outcomes` by
    (irule eval_expr_outcomes_some >>
     gvs[expr_map_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `expr_map_pre _ _ _ _ _` mp_tac >>
  simp[expr_map_pre_def, expr_sim_inv_def] >> strip_tac >>
  drule_all eval_expr_popped_keys_indexed >> strip_tac >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `es'`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `outcomes_accounts_typed es'.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     gvs[outcomes_accounts_typed_def]) >>
  rename1 `type_place_expr env e = SOME (HashMapT kt vty)` >>
  qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> _`
    (qspec_then `HashMapT kt vty` mp_tac) >>
  simp[] >> Cases_on `res` >> gvs[] >> metis_tac[]
QED

Theorem expr_map_pre_checked_type:
  expr_map_pre cenv cx env obj es /\
  place_type cenv obj = MapPT kt vt ==>
  type_place_expr env obj = SOME (HashMapT kt vt)
Proof
  strip_tac >>
  `place_map_tables_agree_on_defined cenv env /\
   ?bkt bvt. type_place_expr env obj = SOME (HashMapT bkt bvt)` by
    gvs[expr_map_pre_def, expr_sim_inv_def] >>
  drule_all place_type_checked_place_on_defined >>
  simp[value_type_place_def] >> strip_tac >> gvs[]
QED

Theorem mapping_subscript_index_pre:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  eval_expr cx obj es = (INL bres, em) ==>
  expr_map_pre cenv cx env obj es /\
  expr_sim_inv cenv cx env em /\
  expr_body_pre cenv cx env idx em
Proof
  strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  drule_all expr_map_pre_eval_result >> strip_tac >>
  simp[] >> irule expr_subscript_pre_index >>
  simp[] >> qexistsl_tac [`ann`, `es`, `obj`] >> simp[]
QED

Theorem expr_map_pre_gas_obs[simp]:
  expr_map_pre cenv cx env e (es with gas_obs := gs) <=>
  expr_map_pre cenv cx env e es
Proof
  simp[expr_map_pre_def]
QED

Theorem mapping_subscript_marked_index_pre:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec memory (ctx, func) (eval_expr cx obj)
    (es, s0) marks (INL tv) mid (OK t) ==>
  expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
  ?s u. eval_expr cx obj s = (INL tv, u)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_expr cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv, mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >>
     simp[]) >>
  conj_tac
  >- (drule_at (Pat `eval_expr _ _ _ = _`) (cj 3 mapping_subscript_index_pre) >>
      simp[] >> disch_then irule >>
      conj_tac >- (goal_assum (drule_at Any)) >>
      qexists `ann` >> simp[]) >>
  metis_tac[]
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
