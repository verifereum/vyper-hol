Theory bodyPtrPopNestedLiveUpdate
Ancestors
  bodyPtrPopNestedLiveSource exprSimProps valueEncodingTyping
  placeMemoryPathRebuild vyperPlaceResultTyping vyperTyping
  valueEncoding list rich_list vyperPlaceStatePreservation

Theorem pop_path_update_val_wf:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated ==>
  val_wf tv updated
Proof
  strip_tac >> drule mem_path_offset_sound >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule_all evaluate_subscripts_type >> simp[]) >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV (FRONT vs)))` by
    (fs[value_has_type_def, all_have_type_EVERY] >>
     conj_tac
     >- (simp[LENGTH_FRONT] >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[MEM_FRONT_NOT_NIL]) >>
  irule (cj 1 value_has_type_val_wf) >>
  irule assign_subscripts_type_path_preserves_type >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
