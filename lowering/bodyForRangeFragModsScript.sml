(* Join the linked Range operand, setup, and round paths at their actual cuts. *)
Theory bodyForRangeFragMods
Ancestors
  bodyForRangeRoundMods bodyForRangeNilMods bodyForRoundsBindMods
  bodyForRangeLiteralStartMods bodyForRangeLiteralCodeMods
  bodyForRangeEndpointRunMods bodyForRangeCheckedCodeMods
  bodyForRangeCheckedStartMods bodyForRangeAllocMods bodyForRangeRouteMods
  bodyForEntryInputsMods gasOutcomeFullZeroPrefixMods bodyFullForFacts
  bodyFullPostsMods bodyInvMetadataProps bodySimDeclCases stmtSimProps
  bodyExprPreFacts bodySimModsProps supportedStmtTraverse supportedStmts
  vyperTypeInvariants vyperTypeSystem vyperValue vyperInterpreter finite_map
  compileEnv valueEncoding loweringSlice exprBodyPreProps vyperState stmtSimForParts
  bodyForRangeLiteralRouteOutcomeMods bodyForRangeCheckedRouteOutcomeMods
  bodyForRangeHeaderMods bodyFullForRange gasOutcomeFullPostMods bodyInvCodeProps
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem range_value_layout[local]:
  is_int_type typ /\ evaluate_type tenv typ = SOME tyv ==>
  type_memory_bytes cenv typ = 32 /\ type_memory_size tyv = 32 /\ word_memory_type tyv
Proof
  Cases_on `typ` >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[evaluate_type_def, AllCaseEqs(), type_memory_bytes_def] >>
  rpt strip_tac >> gvs[type_memory_size_def, word_memory_type_def]
QED

Theorem range_checked_bound[local]:
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  ~(?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)) ==>
  n < dimword (:256)
Proof
  strip_tac >>
  drule (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX))) body_range_typing)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  Cases_on `typ` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_formed_type_def, evaluate_type_def, AllCaseEqs(), well_typed_literal_def,
      within_int_bound_def, LET_THM] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  goal_assum (drule_at (Pat `n < _`)) >> simp[bitTheory.TWOEXP_MONO2] >> decide_tac
QED

Theorem range_scope_unused[local]:
  expr_sim_inv_mods mods cenv cx env es /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> drule expr_sim_inv_mods_env >>
  simp[env_consistent_def, env_scopes_consistent_def] >>
  strip_tac >> Cases_on `lookup_scopes id es.scopes` >> simp[] >>
  qpat_assum `!i entry. lookup_scopes i es.scopes = SOME entry ==> _` drule >>
  simp[FLOOKUP_DEF]
QED

Theorem range_checked_source_ready[local]:
  n1 <= n2 /\ Num (n2 - n1) <= bound ==>
  (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id body
        (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od) =
  eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))
Proof
  simp[get_range_limits_def, lift_sum_def, vyperValueTheory.compatible_bound_def,
       check_def, assert_def, ignore_bind_def, FUN_EQ_THM, bind_def, return_def]
QED

Theorem range_literal_source_ready[local]:
  supported_iterator tops typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound /\
  evaluate_type (get_tenv cx) typ = SOME tyv ==>
  n1 <= n2 /\ Num (n2 - n1) <= bound /\
  (!es. eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) es =
     (INL (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))),es)) /\
  eval_stmt cx (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) =
    eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))
Proof
  simp[supported_iterator_def] >> strip_tac >>
  simp[eval_iterator_range_lit] >>
  pure_once_rewrite_tac[evaluate_def] >>
  simp[LET_THM, lift_option_type_def, lift_option_def, bind_def, ignore_bind_def,
       eval_iterator_range_lit, return_def, check_def, assert_def,
       vyperValueTheory.compatible_bound_def, FUN_EQ_THM]
QED

Theorem compile_for_range_frag_full_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Range e1 e2) bound body) ==>
    EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Range e1 e2) bound body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
       (vyperSubscriptOverlap$accesses_stmt (For id typ (Range e1 e2) bound body)) /\
     IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
     IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  (!tenv s tv t. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) ==>
    body_iterator_full_ok_mods mods exps cx (Range e1 e2)) /\
  (!tenv s tv t s1 vs t1 s2 u t2. tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
    eval_iterator cx (Range e1 e2) s1 = (INL vs,t1) /\
    check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
    body_for_full_ok_mods mods exps cx tv id body vs) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) bound body))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Range e1 e2) bound body)))
    (eval_stmt cx (For id typ (Range e1 e2) bound body)) es
Proof
  strip_tac >> rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `cenv' = cenv` by
    (qpat_assum `stmt_env cenv _ _ (For _ _ _ _ _) sa = _`
      (mp_tac o REWRITE_RULE [range_full_outer_env]) >> simp[]) >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_then (fn th => rewrite_tac[th]) contract_inv_cenv_modules >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  irule gas_outcome_full_mods_post_source >>
  qexists_tac `\H res ee G tn t. res = INL () /\
    range_done_mods DF lo d ctx func cenv cx lctx sa sb es s0 G0 tn0 H ee G tn t` >>
  qexists_tac `\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
      !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)` >>
  simp_tac bool_ss [] >> conj_tac
  >- (rpt gen_tac >> simp[range_done_mods_def, range_outer_frame_mods_def] >>
      strip_tac >> qexists_tac `cenv` >> simp[]) >>
  Cases_on `?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)`
  >- suspend "literal" >>
  suspend "checked"
QED

Resume compile_for_range_frag_full_mods[literal]:
  qpat_x_assum `?a1 n1 a2 n2. _` strip_assume_tac >>
  qpat_x_assum `e1 = _` SUBST_ALL_TAC >> qpat_x_assum `e2 = _` SUBST_ALL_TAC >>
  `env.type_defs = get_tenv cx` by
    (drule_then assume_tac expr_sim_inv_mods_env >>
     fs[env_consistent_def, env_context_consistent_def]) >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `is_int_type typ` by fs[well_typed_iterator_def] >>
  drule_all_then (qspec_then `cenv` strip_assume_tac) range_value_layout >>
  drule_all_then assume_tac range_scope_unused >>
  drule_then assume_tac supported_stmt_for_projection >>
  drule_all_then (qspecl_then [`id`,`body`] strip_assume_tac) range_literal_source_ready >>
  irule range_literal_route_outcome_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `tyv` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `exps` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`bindings`,`src`,`tops`] >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cenv`,`env`,`env'`,`ret_ty`,`shadow_func`,`shadow_sa`,`shadow_sb`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_for_range_frag_full_mods[checked]:
  drule_all_then assume_tac range_checked_bound >>
  `!ee. expr_sim_inv_mods mods cenv cx env ee ==> lookup_scopes id ee.scopes = NONE` by
    (rpt strip_tac >> irule range_scope_unused >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ ee` (irule_at Any) >> first_assum ACCEPT_TAC) >>
  irule range_checked_route_outcome_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> irule range_checked_source_ready >> simp[]) >>
  conj_tac >- (gen_tac >> strip_tac >>
    drule_all_then (qspec_then `cenv` ACCEPT_TAC) range_value_layout) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `exps` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`bindings`,`src`,`tops`] >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cenv`,`env`,`env'`,`ret_ty`,`shadow_sa`,`shadow_func`,`shadow_sb`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise compile_for_range_frag_full_mods
