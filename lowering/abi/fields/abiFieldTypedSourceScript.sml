(* TOP-LEVEL: source ABI typing supplies the static-size facts required by
   the physical layout model; complete layouts therefore encode typed tuples. *)
Theory abiFieldTypedSource
Ancestors
  abiFieldSource abiFieldMemory abiFieldLayoutDefs contractABI list pair

Theorem abi_typed_field_static_sizes:
  !tys vs.
    has_types tys vs ==>
    LIST_REL (\ty v. ~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) tys vs
Proof
  rpt gen_tac >> simp_tac bool_ss [has_types_LIST_REL] >> DISCH_TAC >>
  irule LIST_REL_mono >> qexists_tac `has_type` >> simp[] >>
  rpt gen_tac >> rpt strip_tac >> irule (CONJUNCT1 enc_has_static_length) >> simp[]
QED

Theorem enc_typed_tuple_field_bytes:
  !tys vs.
    has_types tys vs ==>
    enc (Tuple tys) (ListV vs) =
      abi_field_bytes (abi_field_head_size (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs))
        (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs)
Proof
  rpt gen_tac >> DISCH_TAC >> irule enc_tuple_head_size >>
  irule abi_typed_field_static_sizes >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_fields_layout_typed_tuple:
  !tys vs arena ss.
    has_types tys vs /\
    abi_fields_layout (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs) arena 0
      (abi_field_head_size (MAP2 (\ty v. (is_dynamic ty, enc ty v)) tys vs)) ss ==>
    read_memory arena (LENGTH (enc (Tuple tys) (ListV vs))) ss = enc (Tuple tys) (ListV vs)
Proof
  rpt gen_tac >> strip_tac >> irule abi_fields_layout_source_tuple >>
  conj_tac >- (irule abi_typed_field_static_sizes >> first_assum MATCH_ACCEPT_TAC) >>
  first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed source ABI field layout: " ^ name)
  end) (DB.thms "abiFieldTypedSource")
