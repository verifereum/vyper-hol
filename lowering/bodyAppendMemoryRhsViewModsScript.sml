(* Recover the current row at the address saved before the Append RHS. *)
Theory bodyAppendMemoryRhsViewMods
Ancestors
  bodyFullPostsMods bodyFullSubscriptCoveredRow bodySimStmtFacts
  exprBodyPreCallSafetyProps exprBodyPreProps nameLoweringProps
  vyperTypeEvalSoundness vyperTypeEvalProofs vyperPlaceResultTyping
  vyperTypeEnv vyperTypeInvariants vyperStatePreservation vyperState
  stateRelProj exprLoweringProps bodyPtrDefs ptrDiscipline wordArgsPtr
  valueEncoding vyperTyping loweringPosts words finite_map exprSimHypsDefs
  venomState bodyFullShadowBodyInv exprSimProps loweringStateRelDefs

Theorem rhs_read_scope_transition[local]:
  expr_body_pre_mods mods cenv cx env e (mid with gas_obs := gs) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL v,fin) ==>
  typed_scope_transition mid fin /\ popped_keys_indexed mid.scopes /\
  state_well_typed mid /\ state_well_typed fin
Proof
  strip_tac >>
  `state_well_typed fin` by
    (drule_all_then strip_assume_tac (SRULE [SF ETA_ss] expr_body_pre_eval_mods) >>
     fs[expr_sim_inv_mods_def]) >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  fs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac bind_split) >>
  simp[sumTheory.sum_distinct] >> strip_tac >>
  drule read_result_state >> disch_then (SUBST_ALL_TAC o SYM) >>
  irule typed_scope_transition_trans >> qexists_tac `mid with gas_obs := gs` >>
  simp[typed_scope_transition_scopes] >>
  irule (cj 2 (cj 5 eval_scc_type_sound_mutual)) >>
  simp[] >> qexistsl_tac [`cx`,`e`,`env`,`INL x`] >> simp[]
QED

Theorem rhs_local_bounds[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
  lookup_var root s = SOME B ==>
  w2n B + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
  s.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then (strip_assume_tac o SRULE [eval_operand_def]) local_ptrs_rel_value >>
  gvs[] >> drule stmt_state_rel_alloca_room >>
  strip_tac >> metis_tac[alloca_room_next_lt]
QED

Theorem rhs_linked_ghost_zero[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at D 0 d cenv cx es G tn s
Proof
  rw[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >> metis_tac[]
QED

Theorem rhs_ghost_kept_zero[local]:
  ghost_kept_at lo cenv es sa G tn s Gf tf ==>
  ghost_kept_at 0 cenv es sa G tn s Gf tf
Proof
  pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC
QED

Theorem append_memory_rhs_view_mods:
  expr_body_pre_mods mods cenv cx env e (mid with gas_obs := gs) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL v,fin) /\
  expr_post_mods H ctx func cenv cx e mid sp sm s fin v vop u /\
  stmt_state_rel H ctx func cenv cx mid s /\
  ghost_inv_at_mods D lo d cenv cx mid G tn s /\
  ghost_inv_at_mods D lo d cenv cx fin Gf tf u /\
  ghost_kept_at lo cenv mid sp G tn s Gf tf /\
  local_ptrs_reserved cenv sp /\
  lookup_scopes id mid.scopes = SOME initial /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
  lookup_var root s = SOME basew /\
  mem_path_offset initial.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  bp = basew + n2w k /\ (0 < sz ==> lo <= w2n basew) ==>
  w2n bp = w2n basew + k /\ lookup_var root u = SOME basew /\
  lo <= w2n bp /\
  w2n bp + type_memory_size (ArrayTV tv (Dynamic cap)) <= u.vs_alloca_next /\
  k + type_memory_size (ArrayTV tv (Dynamic cap)) <= sz /\
  ?entry vs.
    lookup_scopes id fin.scopes = SOME entry /\ entry.type = initial.type /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    mem_path_offset entry.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
    subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
    read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac rhs_read_scope_transition >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `live_memory_result mid (PlaceR (MemoryPlace id path))` by
    (irule live_memory_result_fresh >>
     goal_assum (drule_at (Pat `lookup_scopes _ _ = _`)) >>
     simp[memory_eval_path_def] >> metis_tac[]) >>
  drule_all_then assume_tac live_memory_result_transport >>
  fs[typed_scope_transition_def] >>
  drule_all_then strip_assume_tac scope_pop_trace_lookup >>
  drule_then strip_assume_tac entry_pop_trace_metadata >>
  drule_all_then assume_tac entry_events_valid >>
  rename1 `lookup_scopes id fin.scopes = SOME entry` >>
  `value_has_type initial.type initial.value /\ well_formed_type_value initial.type` by
    (irule scope_well_typed_lookup_scopes >> fs[state_well_typed_def] >> metis_tac[]) >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule scope_well_typed_lookup_scopes >> fs[state_well_typed_def] >> metis_tac[]) >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `w2n basew + sz <= s.vs_alloca_next /\ type_memory_size initial.type <= sz /\
   s.vs_alloca_next < dimword (:256)` by
    (irule rhs_local_bounds >> goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ mid s`)) >>
     metis_tac[]) >>
  `w2n bp = w2n basew + k` by
    (`w2n basew+k < dimword (:256)` by decide_tac >>
     `basew + n2w k = (n2w (w2n basew+k):bytes32)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     pure_asm_rewrite_tac[wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `local_region cenv mid.scopes s id (w2n basew) sz` by simp[local_region_def] >>
  fs[expr_post_mods_def, expr_post_def, locals_kept_def] >>
  `not_fresh_at sp root` by
    (qpat_assum `local_ptrs_reserved cenv sp`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = SOME (PtrVar (Var p) sz1) ==> _`
       (qspecl_then [`id`,`id`,`root`,`sz`,`sz`] mp_tac) >> simp[]) >>
  `lookup_var root u = SOME basew` by
    (qpat_assum `!x w. not_fresh_at sp x /\ lookup_var x s = SOME w ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  drule_then assume_tac rhs_ghost_kept_zero >>
  `ghost_inv_at D 0 d cenv cx mid G tn s /\ ghost_inv_at D 0 d cenv cx fin Gf tf u` by
    metis_tac[rhs_linked_ghost_zero] >>
  `?a. read_result cx (PlaceR (MemoryPlace id path)) fin = (INL a,fin) /\
    value_has_type (ArrayTV tv (Dynamic cap)) a /\
    well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
    k + type_memory_size (ArrayTV tv (Dynamic cap)) <= sz /\
    !mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) a (w2n bp) mem` by suspend "row" >>
  `0 < sz` by (fs[type_memory_size_def] >> decide_tac) >>
  `w2n basew + sz <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ fin u`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac rhs_local_bounds) >>
     disch_then (drule_all_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `lo <= w2n bp /\ w2n bp + type_memory_size (ArrayTV tv (Dynamic cap)) <= u.vs_alloca_next` by
    (rpt conj_tac >> gvs[] >> decide_tac) >>
  qpat_x_assum `value_has_type (ArrayTV tv (Dynamic cap)) a` mp_tac >>
  Cases_on `a` >> simp[value_has_type_def] >> rename1 `ArrayV ar` >>
  Cases_on `ar` >> simp[value_has_type_def] >> strip_tac >>
  qpat_x_assum `bp = basew + n2w k` (fn eq => pure_rewrite_tac[GSYM eq]) >>
  `type_memory_size (ArrayTV tv (Dynamic cap)) + w2n bp <= u.vs_alloca_next` by decide_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rename1 `read_result _ _ _ = (INL (ArrayV (DynArrayV values)),_)` >>
  qexists_tac `values` >> simp[] >>
  qpat_x_assum `read_result _ _ _ = _` mp_tac >>
  Cases_on `read_memory_path entry path` >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def]
QED

Resume append_memory_rhs_view_mods[row]:
  irule subscript_covered_row_read_robust >>
  qpat_assum `entry_pop_trace initial _ entry` (irule_at Any) >>
  qpat_assum `local_region cenv mid.scopes s id _ sz` (irule_at Any) >>
  qpat_assum `ghost_inv_at D 0 d cenv cx mid G tn s` (irule_at Any) >>
  qpat_assum `ghost_inv_at D 0 d cenv cx fin Gf tf u` (irule_at Any) >>
  qpat_assum `evaluate_subscripts initial.type initial.value path = INL v0` (irule_at Any) >>
  qpat_assum `ghost_kept_at 0 cenv mid sp G tn s Gf tf` (irule_at Any) >>
  simp[ghost_kept_at_refl] >> fs[]
QED
Finalise append_memory_rhs_view_mods
