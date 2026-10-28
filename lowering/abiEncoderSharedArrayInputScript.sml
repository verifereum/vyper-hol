(* Open array windows: no aggregate has_type/cardinality restriction is introduced. *)
Theory abiEncoderSharedArrayInput
Ancestors
  abiEncoderSharedContract abiEncoderOpenInput abiEncoderOpenInputFrame
  abiEncoderArrayFrame abiEncoderInput abiDecoderFootprint abiDecoderContract
  abiDecoderReentry abiCanonicalWindows abiDecodeRanges
  abiCanonicalArrays abiEncoderSharedMembersCorrect abiEncoderArrayPrefix
  abiEncoderTuple abiEncoderMemory
  valueEncoding contractABI venomState venomMemDefs list rich_list arithmetic words

Theorem abi_encoder_open_array_iff:
  abi_encoder_open_input (AbiDynArray ei asz msz active) at av sb source_cap mem <=>
  ?ty avs. at = Array NONE ty /\ av = ListV avs /\ valid_length NONE avs /\
    asz = abi_member_head_size ty /\ active = is_dynamic ty /\
    32+LENGTH avs*msz <= source_cap /\ mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_open_input ei ty (EL i avs) (sb+32+i*msz) msz mem)
Proof
  simp[Once abi_encoder_open_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_shared_array_input_facts:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s ==>
  valid_length NONE avs /\ LENGTH avs < dimword (:256) /\
  asz = abi_member_head_size ty /\ active = is_dynamic ty /\
  32+LENGTH avs*msz <= source_cap /\
  mem_word_at sb s.vs_memory = n2w (LENGTH avs) /\
  (!i. i < LENGTH avs ==>
    abi_encoder_open_input ei ty (EL i avs) (sb+32+i*msz) msz s.vs_memory) /\
  LIST_REL abi_encoder_structural_valid (REPLICATE (LENGTH avs) ty) avs
Proof
  simp_tac bool_ss [abi_encoder_shared_input_def, abi_encoder_open_array_iff] >>
  strip_tac >> gvs[Excl "enc_def"] >>
  asm_simp_tac (srw_ss()) [valid_length_def, LIST_REL_EL_EQN, EL_REPLICATE] >>
  metis_tac[abi_encoder_open_input_valid]
QED

Theorem abi_encoder_shared_array_selected_input:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s /\
  j < LENGTH avs /\ LENGTH (enc ty (EL j avs)) <= output_size /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  abi_decoder_operand_live st.cs_next_var child_src ==>
  abi_encoder_shared_input (ei,ty,EL j avs) (st,child_src,dst)
    (sb+32+j*msz,msz) (d,output_size) (first,last,b,cap) s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `sb+32+j*msz+msz <= sb+source_cap` by
    (`SUC j*msz <= LENGTH avs*msz` by simp[] >>
     pop_assum mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >>
     simp_tac bool_ss [MULT_COMM] >> decide_tac) >>
  `regions_disjoint (sb+32+j*msz,msz) (d,output_size)` by
    (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  `abi_footprint_disjoint (sb+32+j*msz) msz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`,`source_cap`] >> simp[] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def] >> decide_tac
QED

Theorem abi_encoder_open_array_length:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs ==>
  LENGTH (enc (Array NONE ty) (ListV avs)) =
    32 + LENGTH avs*abi_member_head_size ty + SUM (MAP (abi_member_tail_size ty) avs)
Proof
  strip_tac >> simp_tac bool_ss [canonical_array_tuple, LENGTH_APPEND, LENGTH_enc_number] >>
  drule abi_encoder_open_tuple_length >> simp[uniform_member_sizes]
QED

Theorem abi_encoder_open_array_prefix_complete:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d mem ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) mem =
    enc (Array NONE ty) (ListV avs)
Proof
  strip_tac >>
  `head_lengths (REPLICATE (LENGTH avs) ty) 0 = LENGTH avs*abi_member_head_size ty` by
    simp[head_lengths_acc, uniform_member_sizes] >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [abi_encoder_array_prefix_def]) >>
  `mem_bytes_at (d+32) (LENGTH (enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs))) mem =
    enc (Tuple (REPLICATE (LENGTH avs) ty)) (ListV avs)` by
    (irule abi_encoder_open_tuple_prefix_complete >> simp[]) >>
  `mem_bytes_at d (LENGTH (enc_number (Uint 256) (NumV (LENGTH avs)))) mem =
    enc_number (Uint 256) (NumV (LENGTH avs))` by
    simp[abi_encoder_word_window, enc_number_def] >>
  simp_tac bool_ss [canonical_array_tuple] >>
  irule abi_encoder_memory_append >> asm_simp_tac (srw_ss()) [LENGTH_enc_number, Excl "enc_def"]
QED

val _ = List.app (fn th => let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array input admission, axiom or hypothesis"
  end) [abi_encoder_open_array_iff, abi_encoder_shared_array_input_facts,
    abi_encoder_shared_array_selected_input, abi_encoder_open_array_length,
    abi_encoder_open_array_prefix_complete];
