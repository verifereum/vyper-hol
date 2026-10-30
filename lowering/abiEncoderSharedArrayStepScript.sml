(* Open array-prefix algebra.  No execution and no aggregate ABI typing. *)
Theory abiEncoderSharedArrayStep
Ancestors
  abiEncoderSharedArrayInput abiEncoderOpenInput abiEncoderArrayPrefix
  abiEncoderTuple abiEncoderArrayLayout abiEncoderMemory abiCanonicalWindows
  abiDecoderFrame abiDecoderContract valueEncodingProps valueEncoding
  contractABI venomState words list rich_list arithmetic

Theorem abi_encoder_open_array_prefix_lengths[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  j <= LENGTH avs ==>
  LENGTH (FLAT (abi_tuple_heads (LENGTH avs*abi_member_head_size ty) 0
    (REPLICATE j ty) (TAKE j avs))) = j*abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs))) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE j ty) (TAKE j avs)` by
    (gvs[LIST_REL_EL_EQN, LENGTH_TAKE, EL_REPLICATE, EL_TAKE] >> metis_tac[]) >>
  conj_tac
  >- (simp[abi_encoder_open_heads_length] >>
      mp_tac (Q.SPECL [`TAKE j avs`,`ty`] abi_encoder_uniform_sizes) >> simp[]) >>
  simp[abi_tuple_tails_length] >>
  mp_tac (Q.SPECL [`TAKE j avs`,`ty`] abi_encoder_uniform_sizes) >> simp[]
QED

Theorem abi_encoder_open_array_prefix_old_frame[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*abi_member_head_size ty) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) fp ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  strip_tac >> `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  drule_all abi_encoder_open_array_prefix_lengths >> strip_tac >>
  irule abi_encoder_array_prefix_frame >> qexistsl_tac [`fp`,`initial`] >>
  fs[AC ADD_ASSOC ADD_COMM]
QED

Theorem abi_encoder_open_array_static_step:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  j < LENGTH avs /\ ~is_dynamic ty /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*abi_member_head_size ty) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) fp /\
  mem_bytes_at (d+32+j*abi_member_head_size ty) (LENGTH (enc ty (EL j avs)))
    actual.vs_memory = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  strip_tac >> `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_open_array_prefix_lengths >> strip_tac >>
  drule_all abi_encoder_open_array_prefix_old_frame >> disch_tac >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs) /\
   abi_encoder_tuple_prefix (LENGTH avs*abi_member_head_size ty)
     (REPLICATE j ty) (TAKE j avs) (d+32) actual.vs_memory` by
    fs[abi_encoder_array_prefix_def] >>
  irule abi_encoder_array_prefix_advance >> simp[] >>
  irule abi_encoder_tuple_prefix_append >>
  asm_simp_tac (srw_ss()) [] >> simp[mem_bytes_at_def]
QED

Theorem abi_encoder_open_array_dynamic_step:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  j < LENGTH avs /\ is_dynamic ty /\
  off = LENGTH avs*abi_member_head_size ty+
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*abi_member_head_size ty) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) fp /\
  mem_word_at (d+32+j*abi_member_head_size ty) actual.vs_memory = n2w off /\
  mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory =
    enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  strip_tac >> `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_open_array_prefix_lengths >> strip_tac >>
  drule_all abi_encoder_open_array_prefix_old_frame >> disch_tac >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs) /\
   abi_encoder_tuple_prefix (LENGTH avs*abi_member_head_size ty)
     (REPLICATE j ty) (TAKE j avs) (d+32) actual.vs_memory` by
    fs[abi_encoder_array_prefix_def] >>
  irule abi_encoder_array_prefix_advance >> simp[] >>
  irule abi_encoder_tuple_prefix_append >>
  asm_simp_tac (srw_ss()) [LENGTH_enc_number, ADD_ASSOC] >>
  simp[abi_encoder_word_window, enc_number_def] >>
  qpat_x_assum `off = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED
