Theory tuplePlaceZero
Ancestors
  tuplePlaceSource annassignRelayoutPost exprSimFieldLayout
  valueEncodingProps vyperTypeSystem vyperTypeArgFits

(* Zero-capacity diagnostic examples are not assignable destination types.
   At the real consumer the paired fit makes zero source size impossible. *)
Theorem tuple_place_assignable_source_positive:
  assignable_type tenv dty /\ arg_type_fits sty dty /\
  evaluate_type tenv sty = SOME stv ==>
  0 < type_memory_size stv
Proof
  strip_tac >>
  Cases_on `type_memory_size stv = 0`
  >- (drule (cj 1 arg_type_fits_zero_size_rigid) >>
      disch_then drule_all >> strip_tac >> gvs[] >>
      drule_all assignable_type_slot_size_pos >>
      qspec_then `stv` mp_tac slot_count_of_memory_size >> simp[]) >>
  decide_tac
QED

Theorem tuple_place_widened_source_positive:
  assignable_type tenv dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv ==>
  0 < type_memory_size stv
Proof
  rw[type_widens_to_def]
  >- (drule_all assignable_type_slot_size_pos >>
      qspec_then `stv` mp_tac slot_count_of_memory_size >>
      Cases_on `type_memory_size stv = 0` >> simp[]) >>
  metis_tac[tuple_place_assignable_source_positive]
QED

(* At every actual element consumer, not merely for a storage target, the
   frozen root's paired typing excludes the ZERO snapshot alternative. *)
Theorem tuple_place_element_source_positive:
  assignable_type tenv (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type tenv (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys ==>
  0 < type_memory_size (EL i ltvs)
Proof
  strip_tac >> drule_all tuple_place_type_facts >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule tuple_place_widened_source_positive >> metis_tac[]
QED
