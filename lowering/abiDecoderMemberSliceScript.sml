(* Canonical source slices for heterogeneous tuple and struct members.
   TOP-LEVEL: abi_tuple_child_offset_ranges, abi_tuple_child_offset_source.
   Helpers: offset calculation and static-member window. *)
Theory abiDecoderMemberSlice
Ancestors
  abiDecoderCanonicalPtr abiCanonicalWindows abiCanonicalLoad abiDecodeRanges
  abiDecoderContract contractABI venomState words list rich_list arithmetic

Definition abi_tuple_child_offset_def:
  abi_tuple_child_offset tys avs j =
    if is_dynamic (EL j tys) then
      head_lengths tys 0 + SUM (MAP2 abi_member_tail_size (TAKE j tys) (TAKE j avs))
    else SUM (MAP abi_member_head_size (TAKE j tys))
End

Theorem abi_tuple_child_offset_append:
  abi_tuple_child_offset (pre ++ ty::post) (pvs ++ v::rest) (LENGTH pre) =
    if is_dynamic ty then
      head_lengths (pre ++ ty::post) 0 + SUM (MAP2 abi_member_tail_size pre (TAKE (LENGTH pre) (pvs ++ v::rest)))
    else SUM (MAP abi_member_head_size pre)
Proof
  simp[abi_tuple_child_offset_def, TAKE_LENGTH_APPEND, EL_APPEND_EQN]
QED

Theorem abi_tuple_child_offset_ranges:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\ LENGTH pre = LENGTH pvs ==>
  SUM (MAP abi_member_head_size pre) + abi_member_head_size ty <=
    LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) /\
  abi_tuple_child_offset (pre ++ ty::post) (pvs ++ v::rest) (LENGTH pre) +
    LENGTH (enc ty v) <= LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))
Proof
  strip_tac >> drule_all canonical_member_ranges >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_tuple_child_offset_append, TAKE_LENGTH_APPEND, head_lengths_acc, Excl "enc_def"]
QED

Theorem canonical_tuple_static_child_source:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) source =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) ==>
  mem_bytes_at (sb + SUM (MAP abi_member_head_size pre)) (LENGTH (enc ty v)) source = enc ty v
Proof
  strip_tac >>
  `has_type ty v` by fs[has_types_append, has_type_def, Excl "enc_def"] >>
  `LENGTH (enc ty v) = abi_member_head_size ty` by
    (drule (cj 1 enc_has_static_length) >> simp[abi_member_head_size_def]) >>
  drule_all canonical_member_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  irule EQ_TRANS >>
  qexists_tac `TAKE (LENGTH (enc ty v)) (DROP (SUM (MAP abi_member_head_size pre))
    (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))))` >> conj_tac
  >- (qpat_assum `mem_bytes_at sb _ source = _` (fn th =>
        CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
      irule EQ_SYM >> irule mem_bytes_at_window >> asm_simp_tac bool_ss []) >>
  drule_all canonical_member_head_window >> asm_simp_tac bool_ss [LET_THM]
QED

Theorem abi_tuple_child_offset_source:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\ LENGTH pre = LENGTH pvs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))))
    (abi_decode_source opc s) = enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) ==>
  has_type ty v /\
  mem_bytes_at (sb + abi_tuple_child_offset (pre ++ ty::post) (pvs ++ v::rest) (LENGTH pre))
    (LENGTH (enc ty v)) (abi_decode_source opc s) = enc ty v
Proof
  strip_tac >>
  `has_type ty v` by fs[has_types_append, has_type_def, Excl "enc_def"] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac [abi_tuple_child_offset_append] >>
  `TAKE (LENGTH pre) (pvs ++ v::rest) = pvs` by
    (qpat_assum `LENGTH pre = LENGTH pvs`
      (fn th => pure_rewrite_tac [th, TAKE_LENGTH_APPEND]) >> REFL_TAC) >>
  Cases_on `is_dynamic ty`
  >- (drule_all canonical_tuple_dynamic_child_source >>
      asm_simp_tac bool_ss [ADD_ASSOC]) >>
  drule_all canonical_tuple_static_child_source >>
  asm_simp_tac bool_ss []
QED
