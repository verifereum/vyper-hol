(* TOP-LEVEL: storage_subregion describes declared capacity, independently of
   current dynamic lengths. A saved place keeps this provenance across RHS
   effects, including a pop that makes its element temporarily unreachable.
   Helpers: slot-size bounds for tuple components and struct fields. *)
Theory vyperStoragePlaceRegion
Ancestors
  arithmetic list option pair integer vyperState vyperValue vyperPlaceTyping
  vyperStorageWritePreservation

Definition storage_subregion_def:
  storage_subregion tv [] off leaf = (off = 0 /\ leaf = tv) /\
  storage_subregion (ArrayTV elem (Fixed n))
    (ValueSubscript (IntV i)::path) off leaf =
    (0 <= i /\ Num i < n /\
     ?rest. storage_subregion elem path rest leaf /\
            off = Num i * type_slot_size elem + rest) /\
  storage_subregion (ArrayTV elem (Dynamic n))
    (ValueSubscript (IntV i)::path) off leaf =
    (0 <= i /\ Num i < n /\
     ?rest. storage_subregion elem path rest leaf /\
            off = 1 + Num i * type_slot_size elem + rest) /\
  storage_subregion (StructTV fields) (AttrSubscript id::path) off leaf =
    (?delta elem rest. struct_field_slot fields id = SOME (delta,elem) /\
       storage_subregion elem path rest leaf /\ off = delta + rest) /\
  storage_subregion (TupleTV types) (ValueSubscript (IntV i)::path) off leaf =
    (0 <= i /\
     ?elem rest. oEL (Num i) types = SOME elem /\
       storage_subregion elem path rest leaf /\
       off = tuple_prefix_slot_size (Num i) types + rest) /\
  storage_subregion tv path off leaf = F
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND)` >> simp[]
End

Theorem type_slot_size_fields_append:
  !left right. type_slot_size_fields (left ++ right) =
    type_slot_size_fields left + type_slot_size_fields right
Proof
  Induct >> simp[type_slot_size_def] >>
  Cases_on `h` >> simp[type_slot_size_def]
QED

Theorem type_slot_size_fields_sum:
  !fields. type_slot_size_fields fields =
    SUM (MAP (type_slot_size o SND) fields)
Proof
  Induct >> simp[type_slot_size_def] >>
  Cases_on `h` >> simp[type_slot_size_def]
QED

Theorem struct_field_slot_end_bound:
  struct_field_slot fields id = SOME (off,tv) ==>
  off + type_slot_size tv <= type_slot_size (StructTV fields)
Proof
  strip_tac >> drule struct_field_slot_offset >> strip_tac >>
  gvs[type_slot_size_def, type_slot_size_fields_append,
      type_slot_size_fields_sum]
QED

Theorem tuple_component_slot_end_bound:
  !i types tv. oEL i types = SOME tv ==>
    tuple_prefix_slot_size i types + type_slot_size tv <=
    type_slot_size (TupleTV types)
Proof
  Induct >> Cases_on `types` >>
  simp[oEL_def, tuple_prefix_slot_size_def, type_slot_size_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[type_slot_size_def, ADD_COMM]
QED

Theorem array_subregion_end_bound[local]:
  i < n /\ rest + leaf_size <= elem_size ==>
  i * elem_size + rest + leaf_size <= n * elem_size
Proof
  strip_tac >>
  `i * elem_size + elem_size <= n * elem_size` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >>
     simp[]) >> decide_tac
QED

Theorem struct_subregion_end_bound[local]:
  struct_field_slot fields id = SOME (delta,elem) /\
  rest + leaf_size <= type_slot_size elem ==>
  delta + rest + leaf_size <= type_slot_size (StructTV fields)
Proof
  strip_tac >> drule struct_field_slot_end_bound >> decide_tac
QED

Theorem dynamic_subregion_end_bound[local]:
  i < n /\ rest + leaf_size <= type_slot_size elem ==>
  1 + i * type_slot_size elem + rest + leaf_size <=
  type_slot_size (ArrayTV elem (Dynamic n))
Proof
  strip_tac >>
  `i * type_slot_size elem + rest + leaf_size <= n * type_slot_size elem` by
    (irule array_subregion_end_bound >> simp[]) >>
  simp_tac (srw_ss()) [Once type_slot_size_def] >> decide_tac
QED

Theorem tuple_subregion_end_bound[local]:
  oEL i types = SOME elem /\ rest + leaf_size <= type_slot_size elem ==>
  tuple_prefix_slot_size i types + rest + leaf_size <=
  type_slot_size (TupleTV types)
Proof
  strip_tac >> drule tuple_component_slot_end_bound >> decide_tac
QED

Theorem storage_subregion_bounds:
  !tv path off leaf. storage_subregion tv path off leaf ==>
    off + type_slot_size leaf <= type_slot_size tv
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `storage_subregion _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Once storage_subregion_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum (drule_all_then assume_tac) >>
  FIRST [simp_tac (srw_ss()) [Once type_slot_size_def, ADD_ASSOC] >>
           irule array_subregion_end_bound >> simp[],
         irule dynamic_subregion_end_bound >> simp[],
         drule_all struct_subregion_end_bound >> simp[],
         drule_all tuple_subregion_end_bound >> simp[]]
QED

Theorem storage_subregion_append:
  !tv path off mid.
    storage_subregion tv path off mid ==>
    !suffix delta leaf. storage_subregion mid suffix delta leaf ==>
      storage_subregion tv (path ++ suffix) (off + delta) leaf
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  FIRST [qpat_x_assum `storage_subregion _ [] _ _` mp_tac,
         qpat_x_assum `storage_subregion _ (_::_) _ _` mp_tac] >>
  simp_tac (srw_ss()) [Once storage_subregion_def, APPEND] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> simp_tac (srw_ss()) [] >>
  TRY (first_assum ACCEPT_TAC) >>
  first_x_assum (drule_all_then assume_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  pure_once_rewrite_tac [storage_subregion_def] >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED
