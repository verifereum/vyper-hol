(* Source inputs at the entry and the reached base cut of a non-reading subscript. *)
Theory bodyArrayNoCopySourceMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodySimModsProps bodyWriteSubscriptSourceMods
  exprSimSubscriptMap exprSimSource exprSafeOperand exprBodyPreProps
  bodyBranchCellFrameMods bodyNormalHeadTailMods vyperTypeGlobalLookupSoundness
  vyperTypeEvalSoundness vyperTypeEvalCaseProofs vyperEvalOutcomeSuffix
  vyperTypeCallStackSoundness vyperExprNoControl vyperTypeInvariants
  supportedExprTraverse supportedExprs allocLimits gasContext
  exprSimHypsDefs exprSimDefs exprBodyPreCallSafetyProps vyperTypeExprResult
  vyperTypeEnv vyperTypeSystem vyperTypeCallGraph vyperState vyperInterpreter
  vyperAST vyperContext vyperMisc option alist finite_map list
  vyperTypeExprSoundness exprSimSubscriptArraySource bodyFullPredsMods
Libs
  monadsyntax

Theorem array_raw_eval_sound_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e es = (res,ee) ==>
  expr_sim_inv_mods mods cenv cx env ee /\ no_type_error_result res /\
  (case res of INL raw => eval_result_typed (env,cx,ee) raw (Type (expr_type e))
             | INR _ => T)
Proof
  strip_tac >>
  `IS_SOME ee.outcomes` by
    (irule eval_expr_outcomes_some >> fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then assume_tac eval_expr_popped_keys_indexed >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `res`, `ee`] mp_tac) >>
  simp[] >> strip_tac >>
  `outcomes_accounts_typed ee.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >> fs[outcomes_accounts_typed_def]) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem array_raw_admissible_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac array_raw_eval_sound_mods >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_result_typed _ raw _` >> Cases_on `raw` >>
      gvs[eval_result_typed_def]) >>
  drule (cj 1 eval_expr_no_control) >> rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem array_base_typed_mods[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd ==>
  well_typed_expr env obj /\ expr_sim_inv_mods mods cenv cx env es /\
  call_evaluation_safe cx (int_calls_expr obj)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `call_evaluation_safe cx (int_calls_expr obj)` by
    (fs[int_calls_expr_def] >> drule call_evaluation_safe_append_left >> simp[]) >>
  simp[] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule expr_sim_inv_mods_env >> simp[env_consistent_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
  drule type_place_expr_vtype_annotation >> simp[] >>
  Cases_on `vt` >> gvs[vtype_annotation_ok_def] >> strip_tac >> gvs[] >>
  irule type_place_expr_context_value_typed >>
  conj_tac >- (qexists_tac `ArrayT et bd` >> simp[]) >>
  qexists_tac `cx` >> first_assum ACCEPT_TAC
QED

Theorem array_base_type_evaluates[local]:
  env_consistent env cx es /\ well_typed_expr env obj ==>
  IS_SOME (evaluate_type (get_tenv cx) (expr_type obj))
Proof
  strip_tac >> drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, env_consistent_var_type_evaluates] >>
  drule_all well_typed_expr_type_well_formed >> gvs[well_formed_type_def]
QED

Theorem array_nocopy_base_inputs_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx ==>
  ~copies_subscript_base cenv obj idx /\
  well_typed_expr env obj /\ expr_sim_inv_mods mods cenv cx env es /\
  call_evaluation_safe cx (int_calls_expr obj) /\
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type obj)) /\
  (~array_slot_base cenv obj ==> expr_body_pre_mods mods cenv cx env obj es) /\
  (array_slot_base cenv obj ==>
   ?ann' owner id ts tr id_str slot rt.
     obj = TopLevelName ann' (owner,id) /\ ~const_name_root_mods mods obj /\
     ALOOKUP mods owner = SOME ts /\ get_module_code cx owner = SOME ts /\
     find_var_decl_by_name id ts = SOME (StorageVarDecl tr ann',id_str) /\
     lookup_var_slot_from_layout cx tr owner id_str = SOME slot /\
     evaluate_type (get_tenv cx) ann' = SOME rt)
Proof
  simp[linked_subscript_array_context_mods_def] >> strip_tac >>
  drule_all_then strip_assume_tac array_base_typed_mods >>
  drule_all_then assume_tac body_inv_copies_subscript_base_mods >>
  drule_all_then assume_tac array_raw_admissible_mods >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `IS_SOME (evaluate_type (get_tenv cx) (ArrayT et bd))` by
    (drule_all array_base_type_evaluates >> simp[]) >> simp[] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _` mp_tac >>
      simp[expr_body_pre_mods_def, byte_widths_expr_def, alloc_limits_expr_def,
           int_calls_expr_def, expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  strip_tac >>
  `?ann' owner id. obj = TopLevelName ann' (owner,id)` by
    (Cases_on `obj` >> fs[array_slot_base_def] >>
     rename1 `TopLevelName _ nsid` >> PairCases_on `nsid` >> simp[]) >>
  gvs[] >>
  `~cx_const_name_mods mods (owner,id)` by
    fs[expr_body_pre_mods_def, supported_expr_exists_def, const_name_root_mods_def] >>
  `FLOOKUP env.bare_globals (owner,id) = NONE` by
    (Cases_on `FLOOKUP env.bare_globals (owner,id)` >> simp[] >>
     rename1 `FLOOKUP env.bare_globals (owner,id) = SOME bty` >>
     fs[expr_sim_inv_mods_def] >>
     qpat_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _`
       (qspecl_then [`owner`,`id`,`bty`] mp_tac) >>
     qpat_x_assum `array_slot_base _ _` mp_tac >>
     simp[array_slot_base_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP cenv.ce_module_vars (owner,id)` >> gvs[] >>
     rename1 `FLOOKUP cenv.ce_module_vars (owner,id) = SOME loc` >>
     Cases_on `loc` >> simp[]) >>
  drule_all_then assume_tac TopLevelName_toplevel_vtypes_Type >>
  drule_all_then strip_assume_tac env_consistent_toplevel_storage_static >>
  drule_then assume_tac body_const_cells_agree_mods_sources >>
  fs[get_module_code_def, IS_SOME_EXISTS, const_name_root_mods_def] >>
  metis_tac[]
QED

Theorem array_raw_eval_cells_mods[local]:
  well_typed_expr env obj /\ body_const_cells_agree_mods mods cx env es /\
  eval_expr cx obj es = (INL raw,mid) ==>
  body_const_cells_agree_mods mods cx env mid
Proof
  strip_tac >>
  `?res. eval_stmt cx (Expr obj) es = (res,mid)` by
    (simp[Once evaluate_def, bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef raw` >> simp[]) >>
  `type_stmt env NoneT (Expr obj) = SOME env` by
    simp[type_stmt_def, well_typed_expr_not_hashmap_place] >>
  irule body_const_cells_agree_mods_stmt >>
  goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
  qexistsl_tac [`env`,`NoneT`] >> simp[]
QED

Theorem array_nocopy_index_inputs_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  eval_expr cx obj (es with gas_obs := obs) = (INL raw,mid) ==>
  expr_body_pre_mods mods cenv cx env idx mid /\
  body_const_cells_agree_mods mods cx env mid /\
  body_expr_full_ok_mods mods exps cx idx /\ ~is_HashMapRef raw
Proof
  simp[linked_subscript_array_context_mods_def] >> strip_tac >>
  drule_all_then strip_assume_tac array_base_typed_mods >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac array_raw_eval_sound_mods >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then assume_tac array_raw_eval_cells_mods >>
  simp[] >> conj_tac
  >- (irule expr_subscript_pre_index_mods >> simp[] >> qexistsl_tac [`ann`,`es`,`obj`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!s res t s3 res' t'. _` mp_tac >>
      simp[return_def] >> disch_then drule >> simp[]) >>
  Cases_on `raw` >> gvs[eval_result_typed_def, is_HashMapRef_def]
QED
