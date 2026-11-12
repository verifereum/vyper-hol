(* Scalar tuple shape and encoding capacity at the Log store boundary. *)
Theory stmtLogEncodingCapacity
Ancestors
  stmtSimLogEncodeLayout stmtSimLogDataInput vyperTypeABI vyperABI
  compileEnv supportedTypes contractABI list vyperTyping arithmetic words

Theorem log_scalar_embedded_bound[local]:
  supported_scalar_type ty ==>
  vyper_abi_embedded_size env ty =
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
    vyper_abi_size_bound_def, vyper_is_dynamic_def,
    abi_embedded_static_size_def, is_abi_dynamic_def, abi_size_bound_def,
    abi_static_size_def, ceil32_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[supported_word_type_def, supported_string_type_def,
    vyper_abi_size_bound_def, vyper_is_dynamic_def,
    abi_embedded_static_size_def, is_abi_dynamic_def, abi_size_bound_def,
    abi_static_size_def, ceil32_def]
QED

Theorem log_tuple_source_bound[local]:
  !tys. EVERY supported_scalar_type tys ==>
  vyper_abi_size_bound_list env tys = abi_size_bound ce.ce_struct_fields (TupleT tys)
Proof
  Induct >> simp[abi_size_bound_def, Once vyper_abi_size_bound_def] >>
  rpt strip_tac >> simp[log_scalar_embedded_bound]
QED

Theorem log_stored_tuple_encoding_bound:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) tys vs = SOME avs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) tys)) (ListV avs)) <=
    abi_size_bound ce.ce_struct_fields (TupleT tys)
Proof
  strip_tac >> drule_all log_data_layout_typed_tuple >> strip_tac >>
  `vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME (ListV avs)` by
    simp[Once vyper_to_abi_def] >>
  drule_all (cj 1 vyper_to_abi_enc_length_bound) >>
  drule log_tuple_source_bound >>
  strip_tac >> simp[vyper_abi_size_bound_def, vyper_to_abi_type_def] >>
  metis_tac[]
QED

Theorem log_tuple_encoder_shape:
  EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ((?n. type_to_abi_enc_info sf ce (TupleT tys) = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. type_to_abi_enc_info sf ce (TupleT tys) = AbiComplex infos /\
    EXISTS (\(_,_,_,dyn). dyn) infos /\
    EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))
Proof
  strip_tac >> simp[log_tuple_enc_info_selected] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields (TupleT tys)` >> simp[] >>
  conj_tac >- gvs[is_abi_dynamic_def, EXISTS_MAP, combinTheory.o_DEF] >>
  irule log_tuple_enc_members_scalar >> simp[]
QED
