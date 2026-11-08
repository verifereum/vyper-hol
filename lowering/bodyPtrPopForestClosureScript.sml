Theory bodyPtrPopForestClosure
Ancestors bodyPtrPopForest bodyPtrPopForestSource bodyPtrPopForestQueries
  bodyPtrPopInventoryStore bodyPtrPopOwnerReachability bodyPtrDefs
  vyperPlaceResultTyping exprSimProps pred_set

Theorem pop_owner_reachable_step:
  pop_owner_reachable rt initial root fresh /\
  pop_owner_step rt root fresh q root' next ==>
  pop_owner_reachable rt initial root' next
Proof
  metis_tac[pop_owner_reachable_rules]
QED

Theorem pop_retained_forest_header_store:
  pop_retained_forest rt addr Q entry fresh old tn s.vs_memory /\
  pop_owner_reachable rt initial entry.value fresh /\
  well_formed_type_value rt /\ value_has_type rt initial /\
  pop_owner_step rt entry.value fresh q root' next /\
  (evaluate_subscripts rt entry.value q = INL (ArrayV (DynArrayV vs)) \/
   ?err. evaluate_subscripts rt entry.value q = INR err /\
     read_popped rt q fresh = SOME (ArrayV (DynArrayV vs))) /\
  mem_path_offset rt q = SOME (k,ArrayTV et (Dynamic cap)) /\
  t = ((mstore (addr+k) (n2w (LENGTH vs-1)) s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  pop_retained_forest rt addr
    ((q ++ [ValueSubscript (IntV &(LENGTH vs-1))]) INSERT Q)
    (entry with <|value := root'; popped := next ++ old|>) next old tn t.vs_memory
Proof
  strip_tac >> (
  qpat_x_assum `pop_retained_forest _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [pop_retained_forest_def]) >>
  `pop_owner_reachable rt initial root' next` by metis_tac[pop_owner_reachable_step] >>
  `!p v. MEM (p,v) fresh ==> ?kp ptv. mem_path_offset rt p = SOME (kp,ptv) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (addr+kp) m)` by
    metis_tac[] >>
  drule_at (Pat `pop_owner_step _ _ _ _ _ _`) pop_owner_step_robust_store >>
  simp[] >> disch_then (qspecl_then [`tn`, `s`, `initial`, `addr`] mp_tac) >>
  simp[] >> strip_tac >>
  `value_has_type rt root' /\ val_wf rt root' /\ popped_history_typed rt next` by
    metis_tac[pop_reachable_root_typed, pop_reachable_root_wf, pop_reachable_history_typed] >>
  `subscripts_type rt q = SOME (ArrayTV et (Dynamic cap))` by
    metis_tac[mem_path_offset_sound] >>
  drule pop_owner_step_child_read >> simp[] >> strip_tac >>
  simp[pop_retained_forest_def] >> conj_tac
  >- (rpt strip_tac >>
      drule_all pop_reachable_history_owner_typed >> strip_tac >>
      qpat_x_assum `!p v. MEM (p,v) next ==> _` drule >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  rpt strip_tac >- metis_tac[] >>
  `memory_path_covered rt entry.value fresh q'` by simp[memory_path_covered_def] >>
  drule_all pop_owner_step_query_survival >> simp[memory_path_covered_def])
QED
