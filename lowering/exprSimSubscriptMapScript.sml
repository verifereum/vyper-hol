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
  exprSimTopLevelProps compileEnv finite_map
  fragGasPath fragGasMode vyperInterpreter
  vyperTypeEnv vyperStoragePlaceProvenance exprLoweringProps
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
Theorem eval_subscript_bind:
  eval_expr cx (Subscript ann obj idx) =
    bind (eval_expr cx obj) (\tv.
      bind (bind (eval_expr cx idx) (read_result cx)) (\v.
        select_result cx (expr_type obj) tv (ValueSubscript v)))
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_assoc]
QED

Theorem subscript_map_base_admissible:
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es ==>
  gas_admissible (eval_expr cx obj) expr_map_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_map_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _ ==> _` (qspec_then `gs` mp_tac) >>
  rewrite_tac[eval_subscript_bind] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  simp[bind_def]
QED

Theorem subscript_map_index_admissible:
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es /\
  gas_marked_exec memory (ctx, func) (eval_expr cx obj)
    (es, s0) marks (INL tv) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx idx) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  rewrite_tac[eval_subscript_bind] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  gvs[bind_def, expr_map_res_ok_def, expr_res_ok_def]
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
  metis_tac[call_evaluation_safe_append_left]
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
       expr_has_evm_run_thm, EVERY_APPEND, Once supported_expr_exists_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), Once supported_expr_exists_def] >>
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
  gvs[Once supported_expr_exists_def] >>
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
     gvs[expr_map_pre_def]) >>
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
  gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
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
  cheat
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
  cheat
QED
