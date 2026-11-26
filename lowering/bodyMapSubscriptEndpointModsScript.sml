(* Source typing at the actual endpoints of a linked mapping subscript. *)
Theory bodyMapSubscriptEndpointMods
Ancestors
  bodyFullPredsMods bodyBranchCellFrameMods bodySimStmtFacts
  exprBodyPreProps exprSimSubscriptMap exprSimSource exprSimMapDefs exprSimHypsDefs
  vyperTypeEvalSoundness vyperTypeInvariants vyperPlaceResultTyping
  vyperEvalOutcomeSuffix vyperTypeExprSoundness vyperInterpreter vyperState
  vyperAST vyperTypeSystem list option constSubstCorrect vyperConstantFoldReplay
  vyperTypeContractStaticMaps vyperTypeContract finite_map alist
  bodyWriteSubscriptSourceMods

Theorem map_base_eval_typed_mods[local]:
  expr_map_pre_mods mods cenv cx env obj es /\
  type_place_expr env obj = SOME (HashMapT kt vt) /\
  eval_expr cx obj es = (INL (HashMapRef tr slot kt' vt'),mid) ==>
  kt' = kt /\ vt' = vt /\ expr_sim_inv_mods mods cenv cx env mid
Proof
  simp[expr_map_pre_mods_def] >> strip_tac >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then assume_tac eval_expr_outcomes_some >>
  drule_all_then assume_tac eval_expr_popped_keys_indexed >>
  qspecl_then [`cx`, `obj`] (mp_tac o cj 1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`, `es`, `INL (HashMapRef tr slot kt' vt')`, `mid`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!vt. type_place_expr env obj = SOME vt ==> _`
    (qspec_then `HashMapT kt vt` (drule_at (Pos hd))) >>
  simp[NoAsms, eval_result_typed_mapping] >> strip_tac >>
  `outcomes_accounts_typed mid.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >> gvs[outcomes_accounts_typed_def]) >>
  pure_rewrite_tac[expr_sim_inv_mods_def] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!src id ty. _ ==> (src = env.current_src ==> _) /\ _`
    (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[]
QED

Theorem map_index_read_type_mods:
  expr_body_pre_mods mods cenv cx env idx mid /\ expr_type idx = kt /\
  bind (eval_expr cx idx) (read_result cx) mid = (INL v,fin) ==>
  ?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  drule_all_then strip_assume_tac (SRULE [SF ETA_ss] expr_body_pre_eval_mods) >>
  qpat_x_assum `!v'. INL v = INL v' ==> _` (qspec_then `v` mp_tac) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  simp[value_runtime_typed_def]
QED

(* Constructor calls may modify other immutables; retain the declared constant
   cells rather than assuming equality of the entire immutable store. *)
Theorem map_fold_key_origin[local]:
  !mods imms src ts acc out id.
    constants_fold_module mods imms src ts acc = SOME out /\ id IN FDOM out ==>
    id IN FDOM acc \/ ?vis e ty init. MEM (VariableDecl vis (Constant e) id ty init) ts
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  metis_tac[]
QED

Theorem map_fold_cell_frame[local]:
  check_contract mode cx.layouts cx.txn.target mods = SOME art /\
  MEM (src,tops) mods /\ constants_fold_module mods imms src tops FEMPTY = SOME A /\
  A SUBMAP get_source_immutables src imms /\
  (!sid id. declared_constant mods sid id ==>
    FLOOKUP (get_source_immutables sid imms') id = FLOOKUP (get_source_immutables sid imms) id) ==>
  constants_fold_module mods imms' src tops FEMPTY = SOME A /\
  A SUBMAP get_source_immutables src imms'
Proof
  strip_tac >>
  `ALOOKUP mods src = SOME tops` by
    (drule_then assume_tac check_contract_runtime_namespaces >>
     irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  conj_tac
  >- (irule constants_fold_module_replay_present >> reverse conj_tac
      >- (qexists `imms` >> simp[]) >>
      rpt strip_tac >> drule_all check_contract_toplevel_decl_MEM_checked >>
      simp[check_toplevel_decl_def]) >>
  simp[SUBMAP_FLOOKUP_EQN] >> rpt strip_tac >>
  `declared_constant mods src x` by
    (`x IN FDOM A` by metis_tac[flookup_thm] >>
     drule_all map_fold_key_origin >> simp[declared_constant_def] >>
     metis_tac[]) >>
  metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem map_cell_lookup_eq[local]:
  protected_cell_frame addr src id st st' ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP st'.immutables addr of NONE => empty_immutables | SOME imms => imms)) id =
  FLOOKUP (get_source_immutables src
    (case ALOOKUP st.immutables addr of NONE => empty_immutables | SOME imms => imms)) id
Proof
  Cases_on `ALOOKUP st.immutables addr` >>
  Cases_on `ALOOKUP st'.immutables addr` >>
  simp[protected_cell_frame_def, empty_immutables_def, get_source_immutables_def]
QED

Theorem map_base_cells_mods[local]:
  body_const_cells_agree_mods mods cx env es /\
  type_place_expr env obj = SOME (HashMapT kt vt) /\
  eval_expr cx obj es = (res,mid) ==>
  body_const_cells_agree_mods mods cx env mid
Proof
  strip_tac >>
  qpat_x_assum `body_const_cells_agree_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `!addr src id. declared_constant mods src id ==>
      protected_cell_frame addr src id es mid` by
    (rpt strip_tac >>
     `checked_frame_context cx mods art src id env` by
       (simp[checked_frame_context_def] >> qexists `cx.in_deploy` >> simp[]) >>
     drule (cj 5 checked_protected_cell_frame_mutual_aux) >>
     disch_then (drule_at (Pat `checked_frame_context _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qabbrev_tac `imms1 = case ALOOKUP mid.immutables cx.txn.target of
                         NONE => empty_immutables | SOME cells => cells` >>
  `!sid id. declared_constant mods sid id ==>
      FLOOKUP (get_source_immutables sid imms1) id =
      FLOOKUP (get_source_immutables sid imms) id` by
    (unabbrev_all_tac >> rpt strip_tac >>
     qpat_assum `imms = _` SUBST1_TAC >> irule map_cell_lookup_eq >> simp[]) >>
  rewrite_tac[body_const_cells_agree_mods_def] >>
  qexistsl [`roots`,`art`,`imms1`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- simp[Abbr `imms1`]
  >- (rpt strip_tac >>
      qpat_assum `!src tops. MEM _ mods ==> _` (drule_then strip_assume_tac) >>
      drule_all map_fold_cell_frame >> metis_tac[]) >>
  irule checked_eval_expr_or_place_const_cells_agree >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
  qexistsl [`art`,`env`,`mods`] >> simp[] >> metis_tac[]
QED

Theorem map_base_success_mods:
  (expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es) /\
  expr_map_pre_mods mods cenv cx env obj es /\
  type_place_expr env obj = SOME (HashMapT kt vt) /\
  body_const_cells_agree_mods mods cx env es /\
  eval_expr cx obj (es with gas_obs := gs) = (INL (HashMapRef tr slot kt' vt'),mid) ==>
  kt' = kt /\ vt' = vt /\ body_const_cells_agree_mods mods cx env mid /\
  expr_body_pre_mods mods cenv cx env idx mid
Proof
  strip_tac >>
  `expr_map_pre_mods mods cenv cx env obj (es with gas_obs := gs)` by
    fs[expr_map_pre_mods_def] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac map_base_eval_typed_mods >>
  drule_all_then assume_tac map_base_cells_mods >>
  `expr_body_pre_mods mods cenv cx env idx mid` by
    (irule expr_subscript_pre_index_mods >> simp[] >>
     qexistsl [`ann`,`es`,`obj`] >> simp[]) >>
  asm_rewrite_tac[]
QED
