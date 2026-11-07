(* Empty structs pass support but not assignable parameter typing. *)
Theory entrySupportedCardinalityProbe
Ancestors
  supportedTypes vyperTypeContract vyperTypeSystem vyperContext vyperValue
  words list rich_list finite_map arithmetic

Theorem entry_empty_struct_decl[local]:
  check_toplevel_decl mods art src (StructDecl "Empty" [])
Proof
  simp[check_toplevel_decl_def]
QED

Theorem entry_empty_struct_lookup[local]:
  FLOOKUP (type_env [StructDecl "Empty" []]) (NONE,"Empty") = SOME (StructArgs [])
Proof
  simp[type_env_def, type_env_for_module_def, FLOOKUP_UPDATE]
QED

Theorem entry_empty_struct_unassignable[local]:
  ~assignable_type (type_env [StructDecl "Empty" []]) (StructT (NONE,"Empty"))
Proof
  simp[Once assignable_type_def, entry_empty_struct_lookup]
QED

Theorem entry_empty_struct_tuple_unassignable[local]:
  !n. ~assignable_type (type_env [StructDecl "Empty" []])
    (TupleT (REPLICATE n (StructT (NONE,"Empty"))))
Proof
  Cases >> simp[REPLICATE, Once assignable_type_def,
    entry_empty_struct_unassignable]
QED

Theorem entry_empty_struct_tuple_params_rejected:
  ~params_ok (type_env [StructDecl "Empty" []])
    [("x",TupleT (REPLICATE (dimword (:256)) (StructT (NONE,"Empty"))))]
Proof
  simp[params_ok_def, entry_empty_struct_tuple_unassignable]
QED

Theorem entry_empty_struct_tuple_supported[local]:
  !n. 0 < n ==> supported_place_type [StructDecl "Empty" []]
    (TupleT (REPLICATE n (StructT (NONE,"Empty"))))
Proof
  Cases >> simp[REPLICATE, supported_place_type_def,
    Once supported_nested_type_def] >>
  simp[Once supported_nested_type_def, supported_struct_fields_def]
QED

Theorem entry_empty_struct_evaluation[local]:
  evaluate_type (type_env [StructDecl "Empty" []]) (StructT (NONE,"Empty")) =
    SOME (StructTV [])
Proof
  simp[evaluate_type_def, entry_empty_struct_lookup, type_slot_size_def]
QED

Theorem entry_empty_struct_evaluations[local]:
  !n acc. evaluate_types (type_env [StructDecl "Empty" []])
    (REPLICATE n (StructT (NONE,"Empty"))) acc =
    SOME (REVERSE acc ++ REPLICATE n (StructTV []))
Proof
  Induct >> simp[REPLICATE, Once evaluate_type_def] >>
  simp[entry_empty_struct_evaluation, evaluate_type_def, REVERSE_DEF,
    REPLICATE, REPLICATE_APPEND, APPEND_ASSOC]
QED

Theorem entry_empty_struct_tuple_evaluation[local]:
  !n. evaluate_type (type_env [StructDecl "Empty" []])
    (TupleT (REPLICATE n (StructT (NONE,"Empty")))) =
    SOME (TupleTV (REPLICATE n (StructTV [])))
Proof
  gen_tac >>
  `!k. type_slot_size_list (REPLICATE k (StructTV [])) = 0` by
    (Induct >> simp[REPLICATE, type_slot_size_def]) >>
  simp[Once evaluate_type_def, entry_empty_struct_evaluations, type_slot_size_def]
QED

Theorem entry_empty_struct_cardinality_probe:
  supported_place_type [StructDecl "Empty" []]
    (TupleT (REPLICATE (dimword (:256)) (StructT (NONE,"Empty")))) /\
  evaluate_type (type_env [StructDecl "Empty" []])
    (TupleT (REPLICATE (dimword (:256)) (StructT (NONE,"Empty")))) =
    SOME (TupleTV (REPLICATE (dimword (:256)) (StructTV []))) /\
  ~assignable_type (type_env [StructDecl "Empty" []])
    (TupleT (REPLICATE (dimword (:256)) (StructT (NONE,"Empty")))) /\
  ~params_ok (type_env [StructDecl "Empty" []])
    [("x",TupleT (REPLICATE (dimword (:256)) (StructT (NONE,"Empty"))))]
Proof
  simp[entry_empty_struct_tuple_supported, entry_empty_struct_tuple_evaluation,
    entry_empty_struct_tuple_unassignable, entry_empty_struct_tuple_params_rejected]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "supported cardinality probe inherited admission"
  end)
  [entry_empty_struct_decl, entry_empty_struct_lookup,
   entry_empty_struct_unassignable, entry_empty_struct_tuple_unassignable,
   entry_empty_struct_tuple_params_rejected, entry_empty_struct_tuple_supported,
   entry_empty_struct_evaluation, entry_empty_struct_evaluations,
   entry_empty_struct_tuple_evaluation, entry_empty_struct_cardinality_probe];
