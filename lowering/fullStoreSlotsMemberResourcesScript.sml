(* Pure caller resources for joint sparse aggregate composition. *)
Theory fullStoreSlotsMemberResources
Ancestors
  fullStoreSlotsCompositeCases entrySourceEncodingAlignment exprSimProps
  vyperTypeSystem vyperStoragePlaceRegion valueEncodingTyping valueEncodingDefs
  vyperState vyperValue valueEncoding list arithmetic

Theorem store_slots_member_offsets_strict:
  !tvs off limit.
    EVERY (\tv. 0 < type_slot_size tv) tvs /\
    off + type_slot_size_list tvs <= limit ==>
    !i. i < LENGTH tvs ==> off + tuple_prefix_slot_size i tvs < limit
Proof
  Induct >> simp_tac list_ss [type_slot_size_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `i`
  >- (simp[tuple_prefix_slot_size_def] >> decide_tac) >>
  pure_rewrite_tac [tuple_prefix_slot_size_def,LESS_MONO_EQ] >>
  strip_tac >>
  first_x_assum (qspecl_then [`off + type_slot_size h`,`limit`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    qpat_x_assum `off + _ <= limit` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [ADD_ASSOC])) >>
  disch_then (qspec_then `n` mp_tac) >>
  qpat_x_assum `n < _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [ADD_ASSOC]
QED

Theorem store_slots_evaluated_members_positive:
  !tys tvs.
    EVERY (assignable_type tenv) tys /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    EVERY (\tv. 0 < type_slot_size tv) tvs
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt strip_tac >>
  metis_tac[assignable_type_slot_size_pos]
QED
