Theory vyperPlaceProbesTest
Ancestors
  list vyperState vyperTyping vyperPlaceInvariants vyperPlaceResultTyping
Libs
  wordsLib intLib

Theorem tuple_literal_subscript_source_probe:
  subscript_type_ok (TupleT [BaseT BoolT])
    (Literal (BaseT (UintT 256)) (IntL 0)) (BaseT BoolT)
Proof
  EVAL_TAC
QED

Theorem memory_eval_path_tuple_extension_probe:
  lookup_scopes id st.scopes = SOME entry /\
  entry.type = TupleTV [BaseTV BoolT] /\
  entry.value = ArrayV (TupleV [BoolV T]) ==>
  extend_place cx (PlaceR (MemoryPlace id []))
    (ValueSubscript (IntV 0)) st =
    (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV 0)])),st) /\
  memory_eval_path entry.type [ValueSubscript (IntV 0)]
Proof
  rpt strip_tac >>
  gvs[extend_place_def, place_type_value_def, read_place_def,
       read_memory_path_def, get_scopes_def, lift_option_type_def,
       lift_sum_def, bind_def, ignore_bind_def, return_def,
       evaluate_subscripts_def, subscripts_type_def, subscript_type_def,
       vyperValueOperationTheory.array_index_def, oEL_def,
       extend_memory_place_def, memory_eval_path_def]
QED

Theorem tuple_sparse_metadata_probe:
  subscripts_type (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    [ValueSubscript (IntV 0)] = SOME (ArrayTV (BaseTV BoolT) (Fixed 1)) /\
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) [ValueSubscript (IntV 0)] =
    INL (ArrayV (SArrayV [])) /\
  evaluate_subscripts (ArrayTV (BaseTV BoolT) (Fixed 1))
    (ArrayV (SArrayV [])) [ValueSubscript (IntV 0)] = INL (BoolV F) /\
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    (ArrayV (TupleV [ArrayV (SArrayV [])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F)
Proof
  EVAL_TAC
QED

Theorem tuple_metadata_present_dense_probes:
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)])
    (ArrayV (TupleV [ArrayV (SArrayV [(0,BoolV T)])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (BoolV T) /\
  evaluate_subscripts (TupleTV [ArrayTV (BaseTV BoolT) (Dynamic 1)])
    (ArrayV (TupleV [ArrayV (DynArrayV [BoolV T])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (BoolV T) /\
  evaluate_subscripts (TupleTV [TupleTV [BaseTV BoolT]])
    (ArrayV (TupleV [ArrayV (TupleV [BoolV T])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] = INL (BoolV T)
Proof
  EVAL_TAC
QED

Theorem tuple_metadata_nested_sparse_probes:
  evaluate_subscripts
    (TupleTV [StructTV [("f",ArrayTV (BaseTV BoolT) (Fixed 1))]])
    (ArrayV (TupleV [StructV [("f",ArrayV (SArrayV []))]]))
    [ValueSubscript (IntV 0); AttrSubscript "f"; ValueSubscript (IntV 0)] =
    INL (BoolV F) /\
  evaluate_subscripts
    (ArrayTV (TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)]) (Dynamic 1))
    (ArrayV (DynArrayV [ArrayV (TupleV [ArrayV (SArrayV [])])]))
    [ValueSubscript (IntV 0); ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F)
Proof
  EVAL_TAC
QED

Theorem tuple_sparse_delayed_read_probe:
  lookup_scopes id st.scopes = SOME entry /\
  entry.type = TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)] /\
  entry.value = ArrayV (TupleV [ArrayV (SArrayV [])]) /\ entry.popped = [] ==>
  extend_place cx
    (PlaceR (MemoryPlace id [ValueSubscript (IntV 0)]))
    (ValueSubscript (IntV 0)) st =
    (INL (PlaceR (MemoryPlace id
      [ValueSubscript (IntV 0); ValueSubscript (IntV 0)])),st) /\
  read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F)
Proof
  rpt strip_tac >>
  gvs[extend_place_def, place_type_value_def, read_place_def, read_memory_path_def,
      get_scopes_def, lift_option_type_def, lift_sum_def, bind_def, ignore_bind_def,
      return_def, evaluate_subscripts_def, subscripts_type_def, subscript_type_def,
      vyperValueOperationTheory.array_index_def, oEL_def, vyperValueTheory.default_value_def,
      extend_memory_place_def, read_popped_def]
QED

Theorem tuple_sparse_old_history_probe:
  entry.type = TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)] /\
  entry.value = ArrayV (TupleV [ArrayV (SArrayV [])]) /\
  entry.popped = [([ValueSubscript (IntV 0); ValueSubscript (IntV 0)],IntV 7)] ==>
  read_memory_path entry [ValueSubscript (IntV 0); ValueSubscript (IntV 0)] =
    INL (BoolV F) /\ value_has_type (BaseTV BoolT) (BoolV F)
Proof
  rpt strip_tac >>
  gvs[read_memory_path_def, read_popped_def, evaluate_subscripts_def,
      subscripts_type_def, subscript_type_def,
      vyperValueOperationTheory.array_index_def, oEL_def, value_has_type_def,
      rich_listTheory.DROP_LENGTH_APPEND, vyperValueTheory.default_value_def]
QED

Theorem tuple_sparse_trusted_parent_probe:
  entry.type = TupleTV [ArrayTV (BaseTV BoolT) (Fixed 1)] /\
  entry.value = ArrayV (TupleV [ArrayV (SArrayV [])]) ==>
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  memory_history_region entry [] entry.popped [[ValueSubscript (IntV 0)]]
Proof
  rpt strip_tac >>
  gvs[value_has_type_def, well_formed_type_value_def, memory_history_region_def,
      popped_history_typed_def, memory_path_covered_def, evaluate_subscripts_def,
      vyperValueOperationTheory.array_index_def, oEL_def] >> EVAL_TAC
QED

Theorem nested_pop_region_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      before = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1; IntV 2])]);
      middle = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1])]);
      child = [ValueSubscript (IntV 0)];
      fresh1 = record_pop child (ArrayV (DynArrayV [IntV 1; IntV 2])) (IntV 2) [];
      fresh2 = record_pop [] middle (ArrayV (DynArrayV [IntV 1])) fresh1;
      entry = <|assignable := T; type := tv; value := ArrayV (DynArrayV []);
                popped := fresh2 ++ old|>
  in assign_subscripts tv before child PopOp = INL middle /\
     assign_subscripts tv middle [] PopOp = INL entry.value /\
     memory_history_region entry fresh2 old
       [[ValueSubscript (IntV 0); ValueSubscript (IntV 0)];
        [ValueSubscript (IntV 0); ValueSubscript (IntV 1)]]
Proof
  simp[LET_THM, memory_history_region_def, memory_path_covered_def,
    record_pop_def, popped_history_typed_def] >>
  EVAL_TAC >> simp[subscript_type_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, value_has_type_def, well_formed_type_value_def] >>
  rpt strip_tac >> gvs[] >>
  simp[subscripts_type_def, subscript_type_def, vyperASTTheory.bound_length_def] >>
  EVAL_TAC >> simp[value_has_type_def, well_formed_type_value_def,
    wordsTheory.dimword_def]
QED

Theorem unrelated_pop_region_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 3)) (Dynamic 3);
      before = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1]);
                                 ArrayV (DynArrayV [IntV 2])]);
      after = ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 1]);
                                ArrayV (DynArrayV [])]);
      child = [ValueSubscript (IntV 1)];
      fresh = record_pop child (ArrayV (DynArrayV [IntV 2])) (IntV 2) [];
      entry = <|assignable := T; type := tv; value := after;
                popped := fresh ++ old|>
  in assign_subscripts tv before child PopOp = INL after /\
     memory_history_region entry fresh old
       [[ValueSubscript (IntV 0); ValueSubscript (IntV 0)]]
Proof
  simp[LET_THM, memory_history_region_def, memory_path_covered_def,
    record_pop_def, popped_history_typed_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[] >>
  simp[subscripts_type_def, subscript_type_def, vyperASTTheory.bound_length_def] >>
  EVAL_TAC >> simp[value_has_type_def, well_formed_type_value_def,
    wordsTheory.dimword_def]
QED

val _ = List.app (fn name =>
  let val (ors,_) = Tag.dest_tag (Thm.tag (DB.fetch "vyperPlaceProbesTest" name))
  in if List.all (fn s => s = "DISK_THM") ors then ()
     else raise Fail ("oracle dependency in " ^ name) end)
  ["tuple_sparse_metadata_probe", "tuple_metadata_present_dense_probes",
   "tuple_metadata_nested_sparse_probes", "tuple_sparse_delayed_read_probe",
   "tuple_sparse_old_history_probe"];
