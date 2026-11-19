Theory bodyFullSubscriptCoveredRow
Ancestors
  bodyFullSubscriptCurrentRow bodyFullSubscriptHistoryRow
  bodyFullSubscriptObservedRobust bodyFullSubscriptPopLayout
  bodyFullSubscriptPopTraceRead arithmetic words vyperPlaceResultTyping
  vyperPlaceStatePreservation vyperState vyperValueOperation loweringPosts
  exprSimSource exprSimProps bodyPtrDefs loweringStateRelDefs

(* The ordered trace can change a value but cannot add observations to the
   initially live path's layout at the same absolute row address. *)
Theorem covered_row_observations[local]:
  value_has_type initial.type initial.value /\
  well_formed_type_value initial.type /\
  EVERY (\k. ?err. evaluate_subscripts initial.type initial.value k = INR err)
    (MAP FST initial.popped) /\
  entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  read_memory_path entry path = INL v /\
  mem_path_offset entry.type path = SOME (k,tv) ==>
  !i. subscript_layout_byte tv v (b + k) i ==>
      subscript_layout_byte initial.type initial.value b i
Proof
  strip_tac >>
  drule_then strip_assume_tac entry_pop_trace_metadata >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  qabbrev_tac `P = \p t w.
    subscripts_type initial.type p = SOME t /\
    !j i. mem_path_offset initial.type p = SOME (j,t) /\
          subscript_layout_byte t w (b+j) i ==>
          subscript_layout_byte initial.type initial.value b i` >>
  `P [] initial.type initial.value` by
    simp[Abbr `P`, subscripts_type_def, mem_path_offset_def] >>
  `!p t w r t' w'. value_has_type t w /\ P p t w /\
     subscripts_type t r = SOME t' /\ evaluate_subscripts t w r = INL w' /\
     (?old. evaluate_subscripts initial.type initial.value (p ++ r) = INL old) ==>
     P (p ++ r) t' w'` by
    (simp[NoAsms, Abbr `P`] >> rpt strip_tac
     >- metis_tac[vyperPlaceResultTypingTheory.subscripts_type_append] >>
     drule_then strip_assume_tac mem_path_offset_append_decompose >>
     qpat_assum `mem_path_offset initial.type p = SOME _`
       (mp_then Any strip_assume_tac mem_path_offset_sound) >>
     gvs[] >> rename1 `value_has_type parent w` >>
     `well_formed_type_value parent` by
       (qpat_assum `subscripts_type initial.type p = SOME parent`
          (mp_then Any irule subscripts_type_well_formed) >> simp[]) >>
     `subscript_layout_byte parent w (b + d) i` by
       (irule (cj 1 subscript_pop_layout_observation_laws) >>
        qpat_assum `mem_path_offset parent r = SOME _` (irule_at Any) >>
        qpat_assum `evaluate_subscripts parent w r = INL _` (irule_at Any) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        rewrite_tac[GSYM ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!j. subscript_layout_byte parent w _ j ==> _` irule >> simp[]) >>
  `!p t w r et n vs w'. value_has_type t w /\ P p t w /\
     subscripts_type t r = SOME (ArrayTV et (Dynamic n)) /\ vs <> [] /\
     evaluate_subscripts t w r = INL (ArrayV (DynArrayV vs)) /\
     assign_subscripts t w r (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL w' ==>
     P p t w'` by
    (simp[NoAsms, Abbr `P`] >> rpt strip_tac >>
     `well_formed_type_value t` by metis_tac[subscripts_type_well_formed] >>
     `subscript_layout_byte t w (b+j) i` by
       (irule (cj 2 subscript_pop_layout_observation_laws) >> metis_tac[]) >>
     metis_tac[]) >>
  `P path tv v` by
    (irule subscript_pop_trace_tracks_read >>
     qpat_assum `entry_pop_trace initial events entry` (irule_at Any) >>
     qexists `v0` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[Abbr `P`]
QED

Theorem subscript_covered_row_read_robust:
  lookup_scopes id es.scopes = SOME initial /\
  lookup_scopes id fin.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
  lookup_var q s0 = SOME B /\ lookup_var q u = SOME B /\ b = w2n B /\
  local_region ce mid.scopes s id b sz /\
  type_memory_size initial.type <= sz /\
  popped_keys_indexed es.scopes /\
  entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  live_memory_result fin (PlaceR (MemoryPlace id path)) /\
  well_formed_type_value initial.type /\
  value_has_type initial.type initial.value /\ value_has_type entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,tv) /\ w2n a = b+k /\
  ghost_inv_at D0 lo d ce cx es G0 tn0 s0 /\
  ghost_inv_at D1 lo d ce cx fin Gi tni u /\
  popped_kept ce es fin s0 u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gm tnm /\
  ghost_kept_at lo ce mid sm Gm tnm s Gi tni ==>
  ?v. read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
      value_has_type tv v /\ well_formed_type_value tv /\
      k + type_memory_size tv <= sz /\
      !m. mem_agree_outside tni.t_mem u.vs_memory m ==>
          val_in_memory tv v (w2n a) m
Proof
  strip_tac >>
  drule_then strip_assume_tac entry_pop_trace_metadata >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `well_formed_type_value entry.type` by simp[] >>
  `well_formed_type_value tv` by metis_tac[subscripts_type_well_formed] >>
  `local_region ce es.scopes s0 id b sz` by (simp[local_region_def] >> metis_tac[]) >>
  `k + type_memory_size tv <= sz` by gvs[] >>
  Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (rename1 `evaluate_subscripts entry.type entry.value path = INL v` >>
      `w2n a = w2n B + k` by simp[] >>
      `!m. mem_agree_outside tni.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n a) m` by
        (rpt strip_tac >> irule subscript_current_row_robust_path >>
         qpat_assum `ghost_inv_at _ _ _ _ _ fin Gi tni u` (irule_at Any) >>
         qpat_assum `mem_path_offset entry.type path = SOME (k,tv)` (irule_at Any) >>
         qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
         qpat_assum `lookup_scopes id fin.scopes = SOME entry` (irule_at Any) >>
         qpat_assum `lookup_var q u = SOME B` (irule_at Any) >> simp[]) >>
      `value_has_type tv v` by (drule_all evaluate_subscripts_type >> simp[]) >>
      qexists `v` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      simp[read_result_def, read_place_def, get_scopes_def, bind_def,
           lift_option_type_def, lift_sum_def, return_def, read_memory_path_def]) >>
  drule_all subscript_history_row_physical >>
  disch_then (qspec_then `cx` (qx_choose_then `v` strip_assume_tac)) >>
  qexists `v` >> simp[subscript_observed_robust_iff] >> rpt strip_tac >>
  `EVERY (\p. ?err. evaluate_subscripts initial.type initial.value p = INR err)
    (MAP FST initial.popped)` by metis_tac[popped_keys_indexed_lookup_dead] >>
  `subscript_layout_byte initial.type initial.value b i` by
    (irule covered_row_observations >> gvs[] >> metis_tac[]) >>
  `!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
       val_in_memory initial.type initial.value b m` by
    (qpat_x_assum `ghost_inv_at D0 _ _ _ _ _ _ _ _`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_inv_at_def]) >>
     first_x_assum drule_all >> simp[]) >>
  `i NOTIN tn0.t_mem` by
    (qpat_x_assum `!m. mem_agree_outside tn0.t_mem _ m ==> _` mp_tac >>
     gvs[subscript_observed_robust_iff]) >>
  `b <= i /\ i < b + sz` by
    (drule_all (cj 3 subscript_pop_layout_observation_laws) >> decide_tac) >>
  qpat_x_assum `ghost_kept_at _ _ es _ _ _ _ _ _`
    (assume_tac o cj 3 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_x_assum `ghost_kept_at _ _ mid _ _ _ _ _ _`
    (assume_tac o cj 3 o REWRITE_RULE [ghost_kept_at_def]) >>
  metis_tac[]
QED
