(* Stack layout includes singleton tuples and structs. *)
Theory bodyIntCallFamStmtReturnLayout
Ancestors
  stmtSimReturn compileEnv loweringStateRelDefs valueEncoding valueEncodingProofs
  vyperTyping vyperValue list rich_list

Theorem tuple_return_words:
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
  values_have_types tvs vs /\ EVERY is_word_type tys /\
  tuple_in_memory vs tvs (w2n w) mem /\
  w2n w + 32 * LENGTH tys <= dimword (:256) ==>
  intret_vals_match (TupleTV tvs) (ArrayV (TupleV vs))
    (tuple_words ce w tys 0 mem) /\
  LENGTH (tuple_words ce w tys 0 mem) = LENGTH tys
Proof
  strip_tac >>
  `tuple_words ce w tys 0 mem =
   MAP (\(tv,v). typed_val_to_w256 tv v) (ZIP (tvs,vs))` by
    (irule tuple_words_typed >> simp[] >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
  simp[intret_vals_match_def]
QED

Theorem struct_return_words:
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys (MAP SND fts) /\
  struct_has_type fts fields /\ EVERY is_word_type tys /\
  fields_in_memory fields fts (w2n w) mem /\
  w2n w + 32 * LENGTH tys <= dimword (:256) ==>
  intret_vals_match (StructTV fts) (StructV fields)
    (tuple_words ce w tys 0 mem) /\
  LENGTH (tuple_words ce w tys 0 mem) = LENGTH tys
Proof
  strip_tac >>
  drule struct_has_type_values_have_types >> strip_tac >>
  `tuple_in_memory (MAP SND fields) (MAP SND fts) (w2n w) mem` by
    fs[fields_in_memory_tuple] >>
  `tuple_words ce w tys 0 mem =
   MAP (\(tv,v). typed_val_to_w256 tv v)
       (ZIP (MAP SND fts,MAP SND fields))` by
    (irule tuple_words_typed >> simp[] >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `LENGTH (MAP SND fts) = LENGTH tys /\
   LENGTH (MAP SND fields) = LENGTH (MAP SND fts)` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
  simp[intret_vals_match_def]
QED
