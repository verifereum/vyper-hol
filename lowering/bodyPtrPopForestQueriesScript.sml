Theory bodyPtrPopForestQueries
Ancestors bodyPtrPopOwnerReachability bodyPtrPopOwnerPartition
  vyperPlaceResultTyping vyperPlaceStatePreservation vyperLookup
  vyperState vyperValueOperation vyperPlaceInvariants list

Theorem pop_live_owner_query_survival:
  well_formed_type_value rt /\ value_has_type rt root /\
  popped_history_typed rt fresh /\
  subscripts_type rt q = SOME (ArrayTV et (Dynamic cap)) /\
  evaluate_subscripts rt root q = INL arr /\
  popped_value arr = INL child /\ pop_element arr = INL short /\
  assign_subscripts rt root q (Replace short) = INL updated /\
  memory_path_covered rt root fresh r ==>
  memory_path_covered rt updated (record_pop q arr child fresh) r
Proof
  strip_tac >> drule_all assign_subscripts_pop_replace >>
  disch_then (fn th => rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
  irule record_pop_preserves_covered >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem pop_typed_history_member_success:
  popped_history_typed rt history /\ subscripts_type rt r = SOME rtv /\
  MEM (p,v) history /\ IS_PREFIX r p /\ subscripts_type rt p = SOME ptv /\
  evaluate_subscripts ptv v (DROP (LENGTH p) r) = INL w ==>
  ?result. read_popped rt r history = SOME result
Proof
  strip_tac >>
  qspecl_then [`history`, `rt`, `r`, `rtv`] mp_tac read_popped_typed_success_iff >>
  simp[] >> metis_tac[]
QED

Theorem pop_typed_zipper_replace:
  popped_history_typed rt (pre ++ (p,old)::post) /\
  subscripts_type rt p = SOME ptv /\ value_has_type ptv updated ==>
  popped_history_typed rt (pre ++ (p,updated)::post)
Proof
  strip_tac >>
  `well_formed_type_value ptv` by
    (fs[popped_history_typed_def] >>
     first_x_assum (qspecl_then [`p`, `old`] mp_tac) >> simp[]) >>
  fs[popped_history_typed_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem pop_record_success_extend:
  read_popped rt r (record_pop q arr child []) = SOME v ==>
  read_popped rt r (record_pop q arr child history) = SOME v
Proof
  strip_tac >>
  `record_pop q arr child history = record_pop q arr child [] ++ history` by
    (Cases_on `arr` >> simp[record_pop_def] >> Cases_on `a` >> simp[record_pop_def]) >>
  simp[] >> metis_tac[read_popped_prefix_noninterference]
QED

Theorem pop_selected_snapshot_query_survival:
  subscripts_type rt p = SOME ptv /\ well_formed_type_value ptv /\
  value_has_type ptv old /\
  subscripts_type ptv suffix = SOME (ArrayTV et (Dynamic cap)) /\
  evaluate_subscripts ptv old suffix = INL arr /\ pop_element arr = INL short /\
  popped_value arr = INL child /\
  assign_subscripts ptv old suffix (Replace short) = INL updated /\
  evaluate_subscripts ptv old r = INL v /\
  subscripts_type rt (p ++ r) = SOME rtv /\
  popped_history_typed rt (record_pop (p ++ suffix) arr child (pre ++ (p,updated)::post)) ==>
  ?w. read_popped rt (p ++ r) (record_pop (p ++ suffix) arr child (pre ++ (p,updated)::post)) = SOME w
Proof
  strip_tac >> drule_all selected_snapshot_pop_survival >> strip_tac
  >- (irule pop_typed_history_member_success >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`p`, `ptv`, `updated`, `w`] >>
      Cases_on `arr` >> gvs[popped_value_def] >>
      Cases_on `a` >> gvs[popped_value_def, record_pop_def] >>
      simp[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]) >>
  metis_tac[pop_record_success_extend]
QED

Theorem pop_historical_owner_query_survival:
  popped_history_typed rt fresh /\ well_formed_type_value rt /\
  subscripts_type rt q = SOME (ArrayTV et (Dynamic cap)) /\
  read_popped rt q fresh = SOME arr /\ pop_element arr = INL short /\
  popped_value arr = INL child /\ replace_popped rt q short fresh = SOME fresh' /\
  read_popped rt r fresh = SOME v ==>
  ?w. read_popped rt r (record_pop q arr child fresh') = SOME w
Proof
  strip_tac >> drule_all pop_historical_update_zipper >> strip_tac >>
  `well_formed_type_value ptv /\ value_has_type ptv old` by
    (fs[popped_history_typed_def] >>
     first_x_assum (qspecl_then [`p`, `old`] mp_tac) >> simp[]) >>
  `q = p ++ DROP (LENGTH p) q` by
    (drule rich_listTheory.IS_PREFIX_IMP_TAKE >> metis_tac[TAKE_DROP]) >>
  `subscripts_type ptv (DROP (LENGTH p) q) = SOME (ArrayTV et (Dynamic cap))` by
    metis_tac[vyperPlaceResultTypingTheory.subscripts_type_append] >>
  `value_has_type ptv updated` by metis_tac[selected_snapshot_pop_typed] >>
  `popped_history_typed rt fresh'` by
    (metis_tac[pop_typed_zipper_replace]) >>
  `value_has_type (ArrayTV et (Dynamic cap)) arr` by metis_tac[read_popped_type] >>
  `well_formed_type_value et` by
    (drule_all subscripts_type_well_formed >> simp[vyperTypingTheory.well_formed_type_value_def]) >>
  `popped_history_typed rt (record_pop q arr child fresh')` by
    (irule record_pop_history_typed_at_path >> goal_assum (drule_at Any) >> simp[]) >>
  `?rtv. subscripts_type rt r = SOME rtv` by metis_tac[read_popped_declared_type_exists] >>
  qspecl_then [`fresh`, `rt`, `r`, `rtv`] mp_tac read_popped_typed_success_iff >>
  (impl_tac >- simp[]) >> disch_then (mp_tac o iffLR) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  Cases_on `prefix = p /\ snapshot = old`
  >- (gvs[] >>
      `r = p ++ DROP (LENGTH p) r` by
        (drule rich_listTheory.IS_PREFIX_IMP_TAKE >> metis_tac[TAKE_DROP]) >>
      qpat_assum `r = _ ++ _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `q = _ ++ _` (fn th => once_rewrite_tac[th]) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      irule pop_selected_snapshot_query_survival >>
      goal_assum (drule_at Any) >> simp[] >>
      FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC, APPEND] >> metis_tac[]) >>
  `MEM (prefix,snapshot) fresh'` by gvs[] >>
  irule pop_typed_history_member_success >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`prefix`, `htv`, `snapshot`, `w`] >>
  Cases_on `arr` >> gvs[popped_value_def] >>
  Cases_on `a` >> gvs[popped_value_def, record_pop_def]
QED

Theorem pop_owner_step_query_survival:
  pop_owner_step rt root fresh q root' next /\
  well_formed_type_value rt /\ value_has_type rt root /\
  popped_history_typed rt fresh /\
  subscripts_type rt q = SOME (ArrayTV et (Dynamic cap)) /\
  memory_path_covered rt root fresh r ==>
  memory_path_covered rt root' next r
Proof
  strip_tac >> drule pop_owner_step_invert >> strip_tac
  >- (drule_all pop_live_owner_query_survival >> simp[]) >>
  Cases_on `?v. evaluate_subscripts rt root r = INL v`
  >- simp[memory_path_covered_def] >>
  `?v. read_popped rt r fresh = SOME v` by fs[memory_path_covered_def] >>
  drule_all pop_historical_owner_query_survival >> simp[memory_path_covered_def]
QED

Theorem pop_recorded_child_read:
  subscripts_type rt q = SOME (ArrayTV et (Dynamic cap)) /\
  well_formed_type_value et /\ value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  popped_value (ArrayV (DynArrayV vs)) = INL child ==>
  read_popped rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))])
    (record_pop q (ArrayV (DynArrayV vs)) child history) = SOME child
Proof
  strip_tac >>
  `popped_history_typed rt (record_pop q (ArrayV (DynArrayV vs)) child [])` by
    (irule record_pop_history_typed_at_path >> goal_assum (drule_at Any) >>
     simp[popped_history_typed_def]) >>
  `?tv. subscripts_type rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) = SOME tv` by
    (fs[record_pop_def, popped_history_typed_def] >> metis_tac[]) >>
  simp[record_pop_def] >> irule read_popped_new_snapshot >>
  simp[rich_listTheory.IS_PREFIX_REFL, evaluate_subscripts_def] >> metis_tac[]
QED

Theorem pop_owner_step_child_read:
  pop_owner_step rt root fresh q root' next /\
  well_formed_type_value rt /\ value_has_type rt root /\ popped_history_typed rt fresh /\
  subscripts_type rt q = SOME (ArrayTV et (Dynamic cap)) /\
  (evaluate_subscripts rt root q = INL (ArrayV (DynArrayV vs)) \/
   ?err. evaluate_subscripts rt root q = INR err /\
     read_popped rt q fresh = SOME (ArrayV (DynArrayV vs))) ==>
  ?child. read_popped rt (q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) next = SOME child
Proof
  strip_tac >>
  `well_formed_type_value et` by
    (drule_all subscripts_type_well_formed >> simp[vyperTypingTheory.well_formed_type_value_def]) >>
  drule pop_owner_step_invert >> strip_tac >> gs[]
  >- (`value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs))` by
        metis_tac[evaluate_subscripts_type] >>
      drule_all pop_recorded_child_read >> metis_tac[]) >>
  `value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs))` by
    metis_tac[read_popped_type] >>
  drule_all pop_recorded_child_read >> metis_tac[]
QED
