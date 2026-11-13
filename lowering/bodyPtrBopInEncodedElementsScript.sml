(* Index interface for the semantic word lists, including sparse defaults. *)
Theory bodyPtrBopInEncodedElements
Ancestors bodyPtrBopInSemanticList vyperArray vyperTyping vyperValueOperation
  entryDecodeStaticProps list rich_list valueEncoding integer

Theorem membership_dynamic_encoded_length:
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  ws = MAP (typed_val_to_w256 tv) vs ==>
  LENGTH ws = LENGTH vs /\ LENGTH ws <= cap /\
  array_length (ArrayTV tv (Dynamic cap)) (DynArrayV vs) = LENGTH ws
Proof
  simp[value_has_type_def, array_length_def]
QED

Theorem membership_fixed_encoded_length:
  ws = GENLIST (\i. typed_val_to_w256 tv (sparse_val tv kvs i)) cap ==>
  LENGTH ws = cap /\
  array_length (ArrayTV tv (Fixed cap)) (SArrayV kvs) = LENGTH ws
Proof
  simp[array_length_def]
QED

Theorem membership_dynamic_encoded_element:
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  ws = MAP (typed_val_to_w256 tv) vs /\ i < LENGTH ws ==>
  ?v. array_index (ArrayTV tv (Dynamic cap)) (DynArrayV vs) (&i) = SOME v /\
      value_has_type tv v /\ EL i ws = typed_val_to_w256 tv v
Proof
  strip_tac >> gvs[] >> qexists_tac `EL i vs` >>
  simp[array_index_dyn, oEL_THM, EL_MAP] >>
  gvs[value_has_type_def, all_have_type_EVERY, EVERY_EL]
QED

Theorem membership_fixed_encoded_element:
  evaluate_type env et = SOME tv /\
  value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
  ws = GENLIST (\i. typed_val_to_w256 tv (sparse_val tv kvs i)) cap /\
  i < LENGTH ws ==>
  ?v. array_index (ArrayTV tv (Fixed cap)) (SArrayV kvs) (&i) = SOME v /\
      value_has_type tv v /\ EL i ws = typed_val_to_w256 tv v
Proof
  strip_tac >> gvs[] >>
  `value_has_type tv (sparse_val tv kvs i)` by
    (irule sparse_val_has_type >> gvs[value_has_type_def] >> metis_tac[]) >>
  qexists_tac `sparse_val tv kvs i` >> simp[EL_GENLIST] >>
  Cases_on `ALOOKUP kvs i` >> simp[array_index_sarray, sparse_val_def]
QED
