Theory bodyPtrPopForestSource
Ancestors bodyPtrPopReachableSupport bodyPtrPopLiveSupport
  vyperPlaceInvariants exprSimProps valueTypingMemoryProps list

Theorem pop_reachable_root_typed:
  pop_owner_reachable rt initial root fresh /\
  well_formed_type_value rt /\ value_has_type rt initial ==>
  value_has_type rt root
Proof
  strip_tac >> drule_all pop_owner_reachable_support >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  drule pop_live_support_typed >> simp[]
QED

Theorem pop_reachable_history_owner_typed:
  pop_owner_reachable rt initial root fresh /\
  well_formed_type_value rt /\ value_has_type rt initial /\ MEM (p,v) fresh ==>
  ?k tv. mem_path_offset rt p = SOME (k,tv) /\
    well_formed_type_value tv /\ value_has_type tv v /\ val_wf tv v
Proof
  strip_tac >> drule_all pop_owner_reachable_support >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  `?j. j < LENGTH fresh /\ EL j fresh = (p,v)` by metis_tac[MEM_EL] >>
  `?k tv. mem_path_offset rt p = SOME (k,tv) /\
    pop_live_support tv v (0+k) (supps (SUC j))` by metis_tac[] >>
  drule pop_live_support_typed >> strip_tac >>
  qexistsl_tac [`k`, `tv`] >> simp[value_has_type_memory_wf]
QED

Theorem pop_reachable_history_typed:
  pop_owner_reachable rt initial root fresh /\
  well_formed_type_value rt /\ value_has_type rt initial ==>
  popped_history_typed rt fresh
Proof
  strip_tac >> simp[popped_history_typed_def] >> rpt strip_tac >>
  drule_all pop_reachable_history_owner_typed >> strip_tac >>
  drule mem_path_offset_sound >> metis_tac[]
QED

Theorem pop_reachable_root_wf:
  pop_owner_reachable rt initial root fresh /\
  well_formed_type_value rt /\ value_has_type rt initial ==> val_wf rt root
Proof
  metis_tac[pop_reachable_root_typed, value_has_type_memory_wf]
QED
