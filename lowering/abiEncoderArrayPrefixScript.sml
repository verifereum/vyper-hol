(* A dynamic array keeps its count plus the processed heads and tails. *)
Theory abiEncoderArrayPrefix
Ancestors
  abiEncoderArrayLayout abiEncoderTuplePrefix abiEncoderMemory abiCanonicalWindows abiCanonicalArrays
  abiDecodeRanges abiDecoderFrame abiDecoderContract valueEncodingProps valueEncoding contractABI venomState
  words list rich_list arithmetic

Definition abi_encoder_array_prefix_def:
  abi_encoder_array_prefix ty avs j d mem <=>
    j <= LENGTH avs /\ mem_word_at d mem = n2w (LENGTH avs) /\
    abi_encoder_tuple_prefix (LENGTH avs*abi_member_head_size ty)
      (REPLICATE j ty) (TAKE j avs) (d+32) mem
End

Theorem abi_encoder_array_prefix_empty:
  mem_word_at d mem = n2w (LENGTH avs) ==>
  abi_encoder_array_prefix ty avs 0 d mem
Proof
  simp[abi_encoder_array_prefix_def]
QED

Theorem abi_encoder_array_prefix_advance:
  j < LENGTH avs /\ mem_word_at d mem = n2w (LENGTH avs) /\
  abi_encoder_tuple_prefix (LENGTH avs*abi_member_head_size ty)
    (REPLICATE j ty++[ty]) (TAKE j avs++[EL j avs]) (d+32) mem ==>
  abi_encoder_array_prefix ty avs (SUC j) d mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `REPLICATE j ty++[ty] = REPLICATE (SUC j) ty` by
    (PURE_REWRITE_TAC [GSYM SNOC_APPEND, SNOC_REPLICATE] >> REFL_TAC) >>
  `TAKE (SUC j) avs = TAKE j avs++[EL j avs]` by simp[TAKE_SUC, TAKE1_DROP] >>
  full_simp_tac bool_ss [abi_encoder_array_prefix_def] >> decide_tac
QED

Theorem abi_encoder_array_prefix_frame:
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\ abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32)
    (LENGTH (FLAT (abi_tuple_heads (LENGTH avs*abi_member_head_size ty) 0
      (REPLICATE j ty) (TAKE j avs)))) fp /\
  abi_footprint_disjoint (d+32+LENGTH avs*abi_member_head_size ty)
    (LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs)))) fp ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_prefix_def]) >>
  mp_tac (Q.INST [`hl` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty`, `pre` |-> `REPLICATE j ty`,
    `pvs` |-> `TAKE j avs`, `d` |-> `d+32`] abi_encoder_tuple_prefix_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `mload d actual = mload d initial` by
    (irule abi_decode_footprint_frame_mload >> qexists_tac `fp` >> asm_simp_tac bool_ss []) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [mem_word_at_eq_mload]) >>
  asm_simp_tac bool_ss [abi_encoder_array_prefix_def, mem_word_at_eq_mload]
QED

Theorem abi_encoder_array_prefix_complete:
  has_type (Array NONE ty) (ListV avs) /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d mem ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) mem =
    enc (Array NONE ty) (ListV avs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [abi_encoder_array_prefix_def]) >>
  mp_tac (Q.INST [`j` |-> `LENGTH (avs:abi_value list)`] abi_encoder_array_prefix_types) >>
  impl_tac >- simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [TAKE_LENGTH_ID]) >>
  mp_tac (Q.SPECL [`avs`, `ty`] abi_encoder_uniform_sizes) >> strip_tac >>
  `head_lengths (REPLICATE (LENGTH avs) ty) 0 = LENGTH avs*abi_member_head_size ty` by
    asm_simp_tac bool_ss [head_lengths_acc, ADD_CLAUSES] >>
  mp_tac (Q.INST [`tys` |-> `REPLICATE (LENGTH (avs:abi_value list)) ty`, `vs` |-> `avs`, `d` |-> `d+32`]
    abi_encoder_tuple_prefix_complete) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `mem_bytes_at d (LENGTH (enc_number (Uint 256) (NumV (LENGTH avs)))) mem =
    enc_number (Uint 256) (NumV (LENGTH avs))` by
    simp[abi_encoder_word_window, enc_number_def] >>
  simp_tac bool_ss [canonical_array_tuple] >>
  irule abi_encoder_memory_append >> asm_simp_tac (srw_ss()) [LENGTH_enc_number, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array prefix not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayPrefix");
