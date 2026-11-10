(*
 * Expression simulation: compile_subscript_map_case, a case of exprSimPlaces on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimSubscriptMap
Ancestors
  exprSimMapDefs exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimDefs gasContext gasSummary gasSummaryCompose gasExemptCert vyperState
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness supportedExprTraverse allocLimits
  exprOracleStoragePreservation bodyStoragePreservation
  vyperCallOutcomeStorage vyperEvalOutcomeSuffix vyperTypeInvariants
  vyperTypeEvalSoundness vyperTypeExprResult vyperRuntimeAccounts
  vyperExprNoControl vyperPlaceInvariants vyperTypeExprSoundness
  vyperTypeStoragePreservation exprSimMapKey
  vyperStorageLayoutSafety vyperStorageBackend accountsRelProps
  vyperTypeValues vyperLookupStorage
  exprSimTopLevelProps compileEnv loweringStateRelDefs finite_map
  fragGasPath fragGasMode vyperInterpreter
  vyperTypeEnv vyperStoragePlaceProvenance exprLoweringProps
  exprSimSubscriptArraySource
  gasOutcome loweringPosts context venomState

Theorem mapping_leaf_storage_valid:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  contract_storage_well_formed cx es ==>
  slots_in_range (get_storage cx es tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx es tr) slot tv
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  simp[resolve_hashmap_leaf_def] >> strip_tac >>
  conj_tac
  >- (irule contract_storage_well_formed_region >>
      simp[get_storage_backend_eq] >>
      goal_assum (drule_at Any) >> qexists `es` >> simp[]) >>
  irule declared_storage_region_read_live >>
  goal_assum (drule_at Any)
QED

Theorem mapping_leaf_nonoverflow:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  storage_layout_safe cx ==>
  w2n slot + type_slot_size tv <= dimword (:256)
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  simp[resolve_hashmap_leaf_def] >> strip_tac >>
  drule_all storage_layout_safe_region_nonoverflow >> simp[]
QED

Theorem mapping_leaf_storage_holds:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  contract_storage_well_formed cx es /\
  storage_layout_safe cx /\
  stmt_state_rel ctx func cenv cx es s ==>
  storage_holds cx tr typ (PlaceR (StoragePlace tr slot tv)) slot es s
Proof
  strip_tac >> drule_all mapping_leaf_storage_valid >> strip_tac >>
  `w2n slot + type_slot_size tv <= dimword (:256)` by
    (drule_all mapping_leaf_nonoverflow >> simp[]) >>
  `storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot tv` by
    (irule storage_range_agree_of_live >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cx`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, vyperStorageBackendTheory.get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  simp[storage_holds_def, read_result_def, read_place_def,
       read_storage_slot_def, bind_def, lift_option_def, return_def,
       get_storage_backend_eq]
QED

Theorem mapping_leaf_vv_holds:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  contract_storage_well_formed cx es /\
  storage_layout_safe cx /\
  stmt_state_rel ctx func cenv cx es s /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand s = SOME slot ==>
  vv_holds cenv cx typ (PlaceR (StoragePlace tr slot tv))
    (LocatedValue typ p) es s
Proof
  strip_tac >> drule_all mapping_leaf_storage_holds >> strip_tac >>
  Cases_on `tr` >> gvs[vv_holds_def, slot_loc_def]
QED

(* Counted source sequencing keeps the observation stream available to both
   operands; in particular the index is forced only after the base succeeds. *)
Theorem subscript_result_base_admissible:
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es ==>
  gas_admissible (eval_expr cx obj) expr_map_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_map_res_ok_def] >>
  rename1 `INR ex` >>
  first_x_assum irule >>
  qpat_x_assum `!gs res ee. _ ==> _` (qspec_then `gs` mp_tac) >>
  rewrite_tac[eval_expr_subscript_bind] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  simp[bind_def]
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

Theorem subscript_map_base_admissible:
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es ==>
  gas_admissible (eval_expr cx obj) expr_map_res_ok es
Proof
  strip_tac >> irule subscript_result_base_admissible >>
  qexists `expr_map_res_ok` >> simp[] >>
  qexistsl_tac [`ann`, `idx`] >> simp[]
QED

Theorem subscript_map_index_admissible:
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es /\
  gas_marked_exec memory (ctx, func) (eval_expr cx obj)
    (es, s0) marks (INL tv) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx idx) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  strip_tac >> irule subscript_result_index_admissible >>
  goal_assum (drule_at Any) >> qexists `expr_map_res_ok` >> simp[] >>
  qexists `ann` >> simp[]
QED

Theorem subscript_result_predicates_exceptions:
  (!ex. expr_map_res_ok (INR ex) ==> expr_map_res_ok (INR ex)) /\
  (!ex. expr_vv_res_ok (INR ex) ==> expr_map_res_ok (INR ex))
Proof
  simp[expr_vv_res_ok_def, expr_map_res_ok_def]
QED

(* A counted continuation, including its exemption origin, may follow a
   completed result-valued source prefix. *)
Theorem gas_outcome_result_prefix:
  gas_marked_exec memory (ctx, func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es, s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx, func) (k v)
    (mid with gas_obs := [], t) Q R ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists_tac `left ++ right` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`out`, `fin`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_normal >>
                    goal_assum drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ right (err, ef) (callee, tf)` >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  qexistsl_tac [`mid`, `t`, `v`] >>
  simp[GSYM ignore_bind_def]
QED

Theorem gas_outcome_bind_result:
  gas_outcome memory tops (ctx, func)
    (a : evaluation_state -> eval_result evaluation_result) (es, s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!v mid t. P v (mid with gas_obs := []) t ==>
     gas_outcome memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) Q R) ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2
    (mp_tac o REWRITE_RULE [gasOutcomeTheory.gas_outcome_def]) assume_tac) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (gvs[] >> irule gas_outcome_result_prefix >>
          qexistsl_tac [`marks`, `mid`, `t`, `v`] >>
          simp[] >> first_x_assum irule >> simp[]) >>
      gvs[] >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >> simp[]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err, ef) (callee, tf)` >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem gas_outcome_bind_result_exec:
  gas_outcome memory tops (ctx, func)
    (a : evaluation_state -> eval_result evaluation_result) (es, s0) P Exit /\
  (!res ee t. P res ee t ==> ?v. res = INL v) /\
  (!res ee r. Exit res ee r ==> ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!marks v mid t.
     gas_marked_exec memory (ctx, func) a (es, s0) marks (INL v) mid (OK t) /\
     P (INL v) (mid with gas_obs := []) t ==>
     gas_outcome memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) Q R) ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2
    (mp_tac o REWRITE_RULE [gasOutcomeTheory.gas_outcome_def]) assume_tac) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          irule gas_outcome_result_prefix >>
          qexistsl_tac [`marks`, `mid`, `t`, `v`] >>
          simp[] >> first_x_assum irule >> simp[] >>
          goal_assum (drule_at Any)) >>
      `?ex. res = INR ex /\ R (INR ex) (mid with gas_obs := []) r` by
        metis_tac[] >>
      gvs[] >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >> simp[]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err, ef) (callee, tf)` >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem int_calls_subscript_operands:
  !nocalls ann obj idx.
    (nocalls ==> int_calls_expr (Subscript ann obj idx) = []) ==>
    (nocalls ==> int_calls_expr obj = []) /\
    (nocalls ==> int_calls_expr idx = [])
Proof
  simp[int_calls_expr_def]
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

(* Storage preservation accepts both value and place typing.  A mapping
   base uses the latter, not well_typed_expr. *)
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

Theorem expr_map_pre_res_ok:
  !cenv cx env e es res es'.
    expr_map_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_map_res_ok res
Proof
  rpt strip_tac >> drule_all expr_map_pre_eval_result >> strip_tac >>
  Cases_on `res` >> gvs[expr_map_res_ok_def] >>
  drule (cj 1 eval_expr_no_control) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def]
  >~ [`Error err`] >- (Cases_on `err` >> gvs[]) >>
  metis_tac[eval_expr_calls_no_halt, expr_map_pre_def]
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

Theorem mapping_subscript_key_type:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt ==>
  expr_type idx = kt /\ hashmap_key_type kt
Proof
  strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  drule_all expr_map_pre_checked_type >> strip_tac >>
  gvs[expr_body_pre_def, expr_map_pre_def, Once well_typed_expr_def,
      subscript_vtype_def, AllCaseEqs()] >>
  `place_map_tables_agree_on_defined cenv env /\
   (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
              cenv.ce_hashmap_info nsid = NONE)` by
    gvs[expr_sim_inv_def] >>
  drule_all place_type_well_typed_on_defined >> simp[]
QED

Theorem mapping_subscript_key_typed:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  eval_expr cx obj es = (INL bres,em) /\
  (do ir <- eval_expr cx idx; read_result cx ir od) em = (INL kv,en) ==>
  expr_sim_inv cenv cx env en /\ expr_type idx = kt /\
  hashmap_key_type kt /\
  ?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv
Proof
  strip_tac >>
  `expr_body_pre cenv cx env idx em` by
    metis_tac[mapping_subscript_index_pre] >>
  `expr_type idx = kt /\ hashmap_key_type kt` by
    metis_tac[mapping_subscript_key_type] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  metis_tac[]
QED

Theorem mapping_subscript_marked_success:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec memory (ctx,func) (eval_expr cx obj)
    (es,s0) left (INL bres) mid (OK t) /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],t) right (INL kv) fin (OK u) ==>
  expr_sim_inv cenv cx env (fin with gas_obs := []) /\
  expr_type idx = kt /\ hashmap_key_type kt /\
  (?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM fin.scopes
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := [])` by
    (drule_all mapping_subscript_marked_index_pre >> simp[]) >>
  `expr_type idx = kt /\ hashmap_key_type kt` by
    (drule_all mapping_subscript_key_type >> simp[]) >>
  `bind (eval_expr cx idx) (read_result cx)
     (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
     (INL kv,fin with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >> simp[]) >>
  `expr_body_pre cenv cx env idx
     (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by
    (qpat_x_assum `expr_body_pre _ _ _ idx _` mp_tac >> simp[]) >>
  drule_at (Pat `bind _ _ _ = _`)
    (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
  disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (drule (SRULE [SF ETA_ss] exprBopSimPropsTheory.bop_marked_scopes_dom) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >>
     simp[] >> disch_then (mp_tac o MATCH_MP vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  metis_tac[]
QED

Theorem mapping_subscript_selection_success:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt ==>
  ?tv. !tail.
    select_result cx (expr_type obj) (HashMapRef tr slot kt vt)
      (ValueSubscript kv) (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  drule_all expr_map_pre_checked_type >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_map_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `~well_typed_expr env obj` by
    (strip_tac >>
     `place_map_tables_agree_on_defined cenv env /\
      (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
                 cenv.ce_hashmap_info nsid = NONE)` by
       gvs[expr_map_pre_def, expr_sim_inv_def] >>
     drule_all place_type_well_typed_on_defined >> simp[]) >>
  Cases_on `vt`
  >- (rename1 `MapPT kt (Type leaf)` >>
      `ann = leaf /\ well_formed_type env.type_defs leaf` by
        (gvs[expr_body_pre_def, expr_map_pre_def, well_typed_expr_def,
             subscript_vtype_def, AllCaseEqs()]) >>
      gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
      drule vyperHashMapStorageTheory.select_result_hashmap_leaf >>
      disch_then (fn th => simp[th])) >>
  simp[vyperHashMapStorageTheory.select_result_hashmap_nested]
QED

Theorem forced_then_outcome_exec[local]:
  gas_outcome memory tops (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. expr_exit res r) /\
  (!marks v mid t.
    gas_marked_exec memory (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      marks (INL v) mid (OK t) /\ P v (mid with gas_obs := []) t ==>
    ?res ee' r.
      (!tail. k v (mid with gas_obs := tail) =
              (res,ee' with gas_obs := tail)) /\
      gas_marked_path memory ctx func t 0 r /\
      ((?t'. r = OK t' /\ Q res (ee' with gas_obs := []) t') \/
       (exit_result r /\ R res (ee' with gas_obs := []) r))) /\
  (!ex ee r. expr_exit (INR ex : value + exception) r ==>
             R (INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2
    (mp_tac o REWRITE_RULE [gasOutcomeTheory.gas_outcome_def]) assume_tac) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (gvs[] >>
          first_x_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
          (impl_tac >- first_assum ACCEPT_TAC) >>
          disch_then (qx_choose_then `res` (qx_choose_then `ee'`
            (qx_choose_then `rr` (CONJUNCTS_THEN2 assume_tac
              (CONJUNCTS_THEN2 assume_tac assume_tac))))) >>
          `gas_marked_exec memory (ctx,func) (k v)
             (mid with gas_obs := [],t) [] res ee' rr` by
            simp[gas_marked_exec_def] >>
          `gas_marked_exec memory (ctx,func)
             (bind (bind (eval_expr cx e) (read_result cx)) k)
             (es,s0) (marks ++ []) res ee' rr` by
            (irule gas_marked_exec_bind_normal >> goal_assum drule >> simp[]) >>
          rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
          qexists_tac `marks` >> disj1_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`res`, `ee'`, `rr`] >> fs[]) >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
      rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> simp[] >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err, ef) (callee, tf)` >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  pure_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Theorem gas_outcome_conseq:
  gas_outcome memory tops p source start Q R /\
  (!res ee t. Q res ee t ==> Q' res ee t) /\
  (!res ee r. R res ee r ==> R' res ee r) ==>
  gas_outcome memory tops p source start Q' R'
Proof
  PairCases_on `p` >> PairCases_on `start` >>
  pure_rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  metis_tac[]
QED

Theorem compile_mapping_subscript_outcome:
  expr_map_case nocalls ctx func cenv cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==>
            expr_sim_case nocalls ctx func cenv cx idx) /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  (nocalls ==> int_calls_expr (Subscript ann obj idx) = []) /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?tr base_slot kv tv tp p.
       res = INL tv /\
       storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
       select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
         (ValueSubscript kv) ee = (INL tv,ee) /\
       expr_type idx = kt /\ hashmap_key_type kt /\
       (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
                 value_has_type key_ty kv) /\
       expr_sim_inv cenv cx env ee /\ vv = LocatedValue tp p /\
       p.ptr_location = slot_loc tr /\
       eval_operand p.ptr_operand t =
         SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
       stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es ee sa s0 t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp` by
    (Cases_on `is_bytestring_type kt`
     >- (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >> strip_tac >>
         qspecl_then [`key`, `F`, `sn`] mp_tac
           ci_mono_compile_keccak256_key >> simp[ci_mono_def]) >>
     fs[] >> simp[cs_extends_refl]) >>
  `cs_extends sp sb` by
    (qspecl_then [`vv_operand bvv`, `hashed`, `sp`] mp_tac
       ci_mono_compile_mapping_subscript >> simp[ci_mono_def]) >>
  `cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sp sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule exprOperandVarTheory.compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  qpat_assum `compile_expr _ _ obj _ = _`
    (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
  simp[] >> disch_then assume_tac >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  drule_all compile_mapping_operand_not_label >> disch_then assume_tac >>
  `gas_admissible (eval_expr cx obj) expr_map_res_ok es` by
    (irule subscript_result_base_admissible >>
     qexistsl_tac [`A`, `ann`, `idx`] >> simp[]) >>
  `nocalls ==> int_calls_expr obj = []` by
    metis_tac[int_calls_subscript_operands] >>
  `expr_map_sim ctx func cenv cx ty obj es` by
    (qpat_x_assum `expr_map_case _ _ _ _ _ _` mp_tac >>
     simp[expr_map_case_def] >> disch_then irule >> simp[] >>
     qexists `env` >> simp[]) >>
  qpat_x_assum `expr_map_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_map_sim_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[eval_expr_subscript_bind] >>
  disch_then (mp_then Any irule gas_outcome_bind_result_exec) >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[] >> rpt strip_tac >> simp[]) >>
      rpt gen_tac >> simp[] >> rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee t. _) _ _ _` mp_tac >>
  simp[] >> strip_tac >>
  rename1 `v = HashMapRef tr base_slot bkt bvt` >>
  `wb_frame cenv es (mid with gas_obs := []) sa s0 t` by
    (pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` kall_tac >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` kall_tac >>
  qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ t.vs_memory = _` kall_tac >>
  qpat_x_assum `locals_kept cenv es (mid with gas_obs := []) s0 t` kall_tac >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
   ?s u. eval_expr cx obj s = (INL v,u)` by
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)
       mapping_subscript_marked_index_pre >>
     disch_then irule >> simp[] >>
     qexists `ann` >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx idx` by metis_tac[] >>
  `eval_expr cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >>
     disch_then (CONJUNCTS_THEN2 (qspec_then `[]` mp_tac) kall_tac) >> simp[]) >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `bkt = kt /\ bvt = vt` by
    (qpat_assum `eval_expr _ _ (_ with gas_obs := _) = _`
       (mp_then Any mp_tac expr_map_pre_eval_result) >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum (qspec_then `HashMapT kt vt` mp_tac) >>
     simp[eval_result_typed_def]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx))
     expr_res_ok (mid with gas_obs := [])` by
    (irule subscript_result_index_admissible >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`A`, `ann`] >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `nocalls ==> int_calls_expr idx = []` by
    metis_tac[int_calls_subscript_operands] >>
  `expr_sim ctx func cenv cx (expr_type idx) idx (mid with gas_obs := [])` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ _` mp_tac >>
     simp[expr_sim_case_def] >> disch_then irule >> simp[] >>
     qexists `env` >>
     qpat_x_assum `expr_body_pre _ _ _ idx _` mp_tac >> simp[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_def] >>
  disch_then (qspecl_then [`sm`, `sn`, `key`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then assume_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ (start,t)` >>
  irule forced_then_outcome_exec >>
  conj_tac >- metis_tac[stmtSimPropsTheory.expr_exit_INR_type] >>
  qexists_tac `\kv ee u. expr_post ctx func cenv cx idx
    (mid with gas_obs := []) sm sn t ee kv key u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts` >>
  reverse conj_tac >- (simp[Abbr `start`] >> first_assum ACCEPT_TAC) >>
  simp[Abbr `start`] >>
  map_every qx_gen_tac [`imarks`, `kv`, `fin`, `it`] >> strip_tac >>
  `expr_sim_inv cenv cx env (fin with gas_obs := []) /\
   expr_type idx = kt /\ hashmap_key_type kt /\
   (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
             value_has_type key_ty kv) /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (drule_all mapping_subscript_marked_success >> simp[]) >>
  `?selected. !tail.
     select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
       (ValueSubscript kv) (fin with gas_obs := tail) =
     (INL selected,fin with gas_obs := tail)` by
    (irule mapping_subscript_selection_success >>
     qexistsl_tac [`ann`, `cenv`, `env`, `es`, `idx`] >> simp[]) >>

  `fn_has_code sn sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `~it.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `eval_operand (vv_operand bvv) t = SOME base_slot` by
    gvs[contextTheory.vv_operand_def] >>
  `?out. gas_marked_path F ctx func it 0 (OK out) /\
     eval_operand slot out = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
     stmt_state_rel ctx func cenv cx (fin with gas_obs := []) out /\
     wb_frame cenv (mid with gas_obs := []) (fin with gas_obs := []) sm t out /\
     out.vs_current_bb = sb.cs_current_bb /\
     out.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (drule compile_mapping_index_success_tail >>
     disch_then irule >> simp[] >> qexists `vv_operand bvv` >> simp[]) >>
  `wb_frame cenv es (fin with gas_obs := []) sa s0 out` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     qpat_assum `wb_frame cenv es (mid with gas_obs := []) sa s0 t`
       (irule_at Any) >>
     qpat_assum `wb_frame cenv (mid with gas_obs := []) _ sm t out`
       (irule_at Any) >>
     qpat_assum `stmt_state_rel _ _ _ _ es s0` (irule_at Any) >> simp[]) >>
  `storage_mapping_region cx tr base_slot (HashMapT kt vt)` by
    (qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >> simp[]) >>
  qexistsl_tac [`INL selected`, `fin with gas_obs := []`, `OK out`] >>
  simp[] >> qexistsl_tac [`tr`, `base_slot`, `kv`] >>
  simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (fin with gas_obs := []) out` mp_tac >>
  simp[stmt_state_rel_def, state_rel_gas_obs] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem toplevel_storage_ce_vars_decl:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (d,id_str) /\
  lookup_var_slot_from_layout cx (var_decl_transient d) src id_str = SOME slot ==>
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if var_decl_transient d then TransientLoc (n2w slot)
          else StorageLoc (n2w slot))
Proof
  strip_tac >> Cases_on `var_decl_transient d` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  first_x_assum irule >> simp[]
QED

Theorem toplevel_mapping_marked_exec:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vt,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\ ~s0.vs_halted ==>
  gas_marked_exec F (ctx,func) (eval_expr cx (TopLevelName ann (src,id)))
    (es,s0) [] (INL (HashMapRef tr (n2w slot) kt vt)) es (OK s0)
Proof
  strip_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
       Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM]
QED

Theorem compile_toplevel_map_sim:
  expr_map_pre cenv cx env (TopLevelName ann (src,id)) es ==>
  expr_map_sim ctx func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >>
  `env_consistent env cx es /\
   ?kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt)` by
    gvs[expr_map_pre_def, expr_sim_inv_def, well_typed_expr_def,
        AllCaseEqs()] >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout cx tr src id_str = SOME slot` >>
  drule_all lookup_global_mapping >> strip_tac >>
  `storage_mapping_region cx tr (n2w slot) (HashMapT kt vt)` by
    (irule lookup_global_mapping_region >> qexistsl [`src`, `es`, `es`, `id`] >>
     simp[]) >>
  rw[expr_map_sim_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_storage_ce_vars_decl >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
        (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, vyperASTTheory.expr_type_def]) >>
  gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL (HashMapRef tr (n2w slot) kt vt)`, `es`, `OK s0`] >>
  conj_tac >- (irule toplevel_mapping_marked_exec >> simp[]) >>
  disj1_tac >> simp_tac std_ss [] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp_tac std_ss (#rewrs (TypeBase.simpls_of ``:venom_state``))) >>
  qexists `s0` >> simp_tac std_ss [] >>
  qexistsl [`tr`, `n2w slot`, `kt`, `vt`] >>
  simp[slot_loc_def, mk_ptr_def, eval_operand_def, locals_kept_def]
QED

(* A top-level mapping variable: compile_expr lowers it to a pointer
   literal holding the mapping's declared slot (env_consistent's hashmap
   clause, lookup_global_mapping_region), and the source lookup returns the
   HashMapRef at that slot. *)
Theorem compile_toplevel_map_case:
  !nocalls ctx func cenv cx ty id.
    expr_map_case nocalls ctx func cenv cx (TopLevelName ty id)
Proof
  rpt gen_tac >> PairCases_on `id` >>
  rw[expr_map_case_def] >>
  irule compile_toplevel_map_sim >> goal_assum (drule_at Any)
QED

(* A mapping that is a value of a mapping (m[a] for m : HashMap[K,
   HashMap[...]]): the base's slot, the key lowered after it, and
   compile_mapping_subscript's SHA3 over the two (in a fresh 64-byte
   buffer) against hashmap_slot slot (encode_hashmap_key kt kv), with
   compile_keccak256_key for a bytes or string key. *)
Theorem compile_subscript_map_map_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_map_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_map_case_def, expr_map_sim_def] >>
  `expr_map_pre cenv cx env obj es` by
    (drule_all expr_map_pre_subscript_base >> simp[]) >>
  `?kt vt. type_place_expr env obj = SOME (HashMapT kt vt)` by
    fs[expr_map_pre_def] >>
  `place_map_tables_agree_on_defined cenv env` by
    fs[expr_map_pre_def, expr_sim_inv_def] >>
  `place_type cenv obj = MapPT kt vt` by
    (drule_all place_type_checked_place_on_defined >> simp[value_type_place_def]) >>
  irule gas_outcome_conseq >>
  irule_at (Pos last) compile_mapping_subscript_outcome >>
  simp[] >>
  qexistsl_tac [`vv`, `vt`, `ty`, `sb`, `sa`, `nocalls`, `kt`, `env`, `cenv`, `expr_map_res_ok`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `?ikt ivt. vt = HashMapT ikt ivt` by
    (qpat_x_assum `expr_map_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_map_pre_def, Once well_typed_expr_def] >>
     Cases_on `vt` >> simp[subscript_vtype_def, AllCaseEqs()]) >>
  gvs[vyperHashMapStorageTheory.select_result_hashmap_nested] >>
  drule storage_mapping_region_step >> disch_then (qspec_then `kv` assume_tac) >>
  simp[] >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC

QED

(* With every smaller expression simulating, an expression naming a
   mapping simulates: its keys are smaller. *)
Theorem expr_map_case_below:
  !obj cenv ctx func cx.
    expr_sim_below cenv (expr_size obj) ==>
    expr_map_case T ctx func cenv cx obj
Proof
  measureInduct_on `expr_size obj` >> rpt strip_tac >>
  Cases_on `obj`
  >~ [`TopLevelName`] >- simp[compile_toplevel_map_case]
  >~ [`Subscript _ _ _`]
  >- (rename1 `Subscript ann obj0 idx` >>
      irule compile_subscript_map_map_case >> conj_tac
      >- (rpt strip_tac >>
          `expr_ok cenv idx` by
            (fs[expr_sim_below_def] >> first_x_assum irule >>
             simp[expr_size_def]) >>
          gvs[expr_ok_case]) >>
      first_x_assum irule >> simp[expr_size_def] >>
      irule expr_sim_below_mono >>
      qexists_tac `expr_size (Subscript ann obj0 idx)` >>
      simp[expr_size_def]) >>
  irule expr_map_case_other >> simp[]
QED

(* A subscript of a mapping (place_type MapPT) whose value is not a
   mapping: the base's expr_map_case gives the operand holding the
   mapping's slot, the key is lowered after it, and the slot computation
   is compile_subscript_map_map_case's.  expr_sim_inv's map table clauses
   make MapPT mean a declared mapping.  For a storage or transient leaf,
   storage_holds also asks that the leaf's slots are in range
   (slots_in_range); the proof gets that from static_/dyn_slots_in_range
   and the hashmap regions of contract_storage_well_formed, as
   toplevel_storage_slots_in_range and storage_field_slots_in_range do for
   names and struct fields. *)
Theorem compile_subscript_map_case:
  !nocalls ctx func cenv cx ann obj idx kt vt.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >>
  rw[expr_vv_case_def, expr_vv_sim_def] >>
  irule gas_outcome_conseq >>
  irule_at (Pos last) compile_mapping_subscript_outcome >> simp[] >>
  qexistsl_tac [`vv`, `vt`, `ty`, `sb`, `sa`, `nocalls`, `kt`, `env`, `cenv`, `expr_vv_res_ok`] >>
  simp[subscript_result_predicates_exceptions] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    (drule_all expr_body_pre_map_subscript_base >> simp[]) >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  `~well_typed_expr env obj` by
    (metis_tac[well_typed_expr_not_hashmap_place]) >>
  `vt = Type ann` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     Cases_on `vt` >> simp[subscript_vtype_def, AllCaseEqs()]) >>
  `tp = ann` by
    (drule_all compile_expr_mapping_subscript_parts >>
     strip_tac >> gvs[]) >>
  gvs[] >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  simp[select_result_def, extend_place_def, lift_option_type_def,
       lift_option_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `evaluate_type (get_tenv cx) ann` >>
  gvs[raise_def, return_def] >>
  drule storage_mapping_region_step >> disch_then (qspec_then `kv` assume_tac) >>
  `contract_storage_well_formed cx ee /\ storage_layout_safe cx` by
    gvs[expr_sim_inv_def] >>
  drule_all mapping_leaf_storage_valid >> strip_tac >>
  drule_all mapping_leaf_vv_holds >> strip_tac >>
  simp[vv_post_def, expr_type_def, vv_at_def] >>
  conj_tac >- (Cases_on `tr` >> gvs[slot_loc_def]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  strip_tac >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, Cases_on `tr` >> gvs[slot_loc_def] >> NO_TAC]

QED
