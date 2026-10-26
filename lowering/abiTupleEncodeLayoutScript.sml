(* Numeric translation metadata needed to interpret the constructed tuple.
   These conditions concern ABI heads, dynamic flags and static slot sizes. *)
Theory abiTupleEncodeLayout
Ancestors
  abiTupleEncodeMemory abiTupleProps abiEncoderAdmissible abiEncoderInput
  abiEncoderCorrectLeaves abiEncoderMemory abiStaticAggregateProps compileEnv exprLowering
  valueEncoding contractABI words list rich_list arithmetic

Definition abi_tuple_encode_layout_def:
  abi_tuple_encode_layout ce (xs:(operand # type) list) ats <=>
    LIST_REL (\(op,ty) at.
      abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size at /\
      is_abi_dynamic ce.ce_struct_fields ty = is_dynamic at /\
      (~is_dynamic at ==> type_memory_bytes ce ty = static_length at)) xs ats
End

Theorem abi_tuple_encode_layout_lengths:
  abi_tuple_encode_layout ce xs ats ==> LENGTH xs = LENGTH ats
Proof
  simp[abi_tuple_encode_layout_def] >> strip_tac >> drule LIST_REL_LENGTH >> simp[]
QED

Theorem abi_tuple_encode_layout_dynamic:
  !xs ats. abi_tuple_encode_layout ce xs ats ==>
  is_abi_dynamic ce.ce_struct_fields (TupleT (MAP SND xs)) = any_dynamic ats
Proof
  Induct >- simp[abi_tuple_encode_layout_def, is_abi_dynamic_def, is_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> Cases_on `ats` >>
  simp[abi_tuple_encode_layout_def, is_abi_dynamic_def, is_dynamic_def] >> rpt strip_tac >>
  rename1 `LIST_REL _ xs tail_ats` >>
  qpat_x_assum `!ats. _` (qspec_then `tail_ats` mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_tuple_encode_layout_def, is_abi_dynamic_def]
QED

Theorem abi_tuple_encode_layout_static_length:
  !xs ats. abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats ==>
    static_length (Tuple ats) = abi_tuple_bytes ce xs
Proof
  Induct >- simp[abi_tuple_encode_layout_def, static_length_def, abi_tuple_bytes_def] >>
  gen_tac >> PairCases_on `h` >> Cases_on `ats` >>
  simp[abi_tuple_encode_layout_def, static_length_def, abi_tuple_bytes_def, is_dynamic_def] >>
  rpt strip_tac >> rename1 `LIST_REL _ xs tail_ats` >>
  qpat_x_assum `!ats. _` (qspec_then `tail_ats` mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_tuple_encode_layout_def, static_length_def, abi_tuple_bytes_def]
QED

Theorem abi_encoder_static_leaf_window:
  abi_encoder_static_leaf ei /\ abi_encoder_input ei at av sb cap mem /\
  ~is_dynamic at ==>
  mem_bytes_at sb (static_length at) mem = enc at av
Proof
  rw[abi_encoder_static_leaf_def]
  >- fs[abi_encoder_input_word_iff]
  >- fs[abi_encoder_input_copy_iff] >>
  drule abi_encoder_empty_input >> strip_tac >> drule abi_encoder_input_typed >> strip_tac >>
  `static_length at = 0` by (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem abi_tuple_encode_static_window:
  !xs ats avs d mem.
  abi_tuple_encode_memory sf ce xs ats avs d mem /\ abi_tuple_encode_layout ce xs ats /\
  ~any_dynamic ats ==>
  mem_bytes_at d (abi_tuple_bytes ce xs) mem = FLAT (MAP2 enc ats avs)
Proof
  Induct >- simp[abi_tuple_encode_memory_def, abi_tuple_bytes_def, mem_bytes_at_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[abi_tuple_encode_memory_def, abi_tuple_encode_layout_def, is_dynamic_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `abi_encoder_input (type_to_abi_enc_info sf ce h1) head_at head_av d _ mem` >>
  `abi_encoder_static_leaf (type_to_abi_enc_info sf ce h1)` by
    (drule_all abi_encoder_translation_static_leaf >> simp[]) >>
  `mem_bytes_at d (type_memory_bytes ce h1) mem = enc head_at head_av` by
    (drule_all abi_encoder_static_leaf_window >> simp[]) >>
  qpat_x_assum `!ats avs d mem. _`
    (fn th => drule_all (SIMP_RULE bool_ss [abi_tuple_encode_layout_def] th)) >> strip_tac >>
  mp_tac (Q.SPECL [`d`, `type_memory_bytes ce h1`, `abi_tuple_bytes ce (xs:(operand # type) list)`, `mem`]
    abi_encoder_mem_split) >> fs[abi_tuple_bytes_def]
QED
