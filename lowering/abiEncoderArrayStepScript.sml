(* Exact child write windows advance the encoded array prefix and retain its count. *)
Theory abiEncoderArrayStep
Ancestors
  abiEncoderArrayBounds abiEncoderArrayPrefix abiEncoderArrayLayout abiEncoderTupleStep abiEncoderTuplePrefix
  abiCanonicalWindows abiDecoderFrame abiDecoderContract valueEncodingProps valueEncoding
  contractABI venomState words list rich_list arithmetic

Theorem abi_encoder_array_static_step:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\ ~is_dynamic ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ (d+output_size <= b \/ b+cap <= d) /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame [(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)));(b,cap)]
    initial actual /\
  mem_bytes_at (d+32+j*abi_member_head_size ty) (LENGTH (enc ty (EL j avs))) actual.vs_memory =
    enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_sizes >> strip_tac >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_prefix_def]) >>
  `mload d actual = mload d initial` by
    (irule abi_decode_footprint_frame_mload >>
     qexists_tac `[(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)));(b,cap)]` >>
     asm_simp_tac bool_ss [] >>
     full_simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM,
       FORALL_AND_THM, Excl "enc_def"] >> decide_tac) >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs)` by
    full_simp_tac bool_ss [mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`pre` |-> `REPLICATE j ty`, `pvs` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `heads` |-> `j*abi_member_head_size ty`,
    `tails` |-> `SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`,
    `hl` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_encoder_tuple_static_step) >>
  impl_tac >- (full_simp_tac bool_ss [LENGTH_REPLICATE] >> decide_tac) >> disch_tac >>
  irule abi_encoder_array_prefix_advance >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_dynamic_step:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\ is_dynamic ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ (d+output_size <= b \/ b+cap <= d) /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame [(d+32+j*abi_member_head_size ty,32);
    (d+32+off,LENGTH (enc ty (EL j avs)));(b,cap)] initial actual /\
  mem_word_at (d+32+j*abi_member_head_size ty) actual.vs_memory = n2w off /\
  mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_sizes >> strip_tac >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_prefix_def]) >>
  `mload d actual = mload d initial` by
    (irule abi_decode_footprint_frame_mload >>
     qexists_tac `[(d+32+j*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL j avs)));(b,cap)]` >>
     asm_simp_tac bool_ss [] >>
     full_simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM,
       FORALL_AND_THM, Excl "enc_def"] >> decide_tac) >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs)` by
    full_simp_tac bool_ss [mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`pre` |-> `REPLICATE j ty`, `pvs` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `heads` |-> `j*abi_member_head_size ty`,
    `tails` |-> `SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`,
    `hl` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_encoder_tuple_dynamic_step) >>
  impl_tac >- (full_simp_tac bool_ss [LENGTH_REPLICATE] >> decide_tac) >> disch_tac >>
  irule abi_encoder_array_prefix_advance >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_STEP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array prefix step not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayStep");
