Theory abiScratchPrefix
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiEncoderComplexPrefix abiEncoderChildFrames
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry compileEnv venomState finite_map words
  arithmetic abiEncoderArrayFrame abiEncoderArrayBounds abiEncoderArrayPrefix
  abiEncoderArrayLayout abiEncoderTuple abiEncoderMemory abiCanonicalWindows abiDecoderContract
  valueEncodingProps valueEncoding contractABI list rich_list

(* ===== Effect ===== *)

(* Turn an actual cursor initializer's observations into its precise effect.
   TOP-LEVEL: abi_scratch_prefix_effect accounts for the sole allocation site
   and the owned frame without excluding the whole numeric scratch arena. *)

Theorem abi_scratch_prefix_effect:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids site stop) b cap initial) initial actual /\ site < stop ==>
  abi_scratch_effect first last site stop next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids site stop) b cap initial) initial actual` by
    (irule abi_encoder_frame_extra_window >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> rpt gen_tac >> strip_tac >>
  `id <> site` by decide_tac >> simp[]
QED

(* ===== Step ===== *)

(* Processed ABI heads and tails survive a child with physical scratch ownership.
   TOP-LEVEL: abi_scratch_array_dynamic_step advances the output invariant.
   Helpers: arbitrary-footprint window separation and tuple prefix extension. *)

Theorem abi_scratch_prefix_windows:
  heads+head_sz <= hl /\ off = hl+tails /\ off+tail_sz <= output_size /\
  abi_footprint_disjoint d output_size fp ==>
  abi_footprint_disjoint d heads ([(d+heads,head_sz);(d+off,tail_sz)]++fp) /\
  abi_footprint_disjoint (d+hl) tails ([(d+heads,head_sz);(d+off,tail_sz)]++fp)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint d heads fp /\ abi_footprint_disjoint (d+hl) tails fp` by
    (conj_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `output_size`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_footprint_disjoint_append] >>
  simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac
QED

Theorem abi_scratch_tuple_dynamic_step:
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+32 <= hl /\ off = hl+tails /\ off+LENGTH (enc ty av) <= output_size /\
  abi_footprint_disjoint d output_size fp /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decode_footprint_frame ([(d+heads,32);(d+off,LENGTH (enc ty av))]++fp) initial actual /\
  mem_word_at (d+heads) actual.vs_memory = n2w off /\
  mem_bytes_at (d+off) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `32`, `tail_sz` |-> `LENGTH (enc ty av)`]
    abi_scratch_prefix_windows) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`fp` |-> `[(d+heads,32);(d+off,LENGTH (enc ty av))]++fp`]
    abi_encoder_tuple_prefix_frame) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  `mem_bytes_at (d+heads) (LENGTH (enc_number (Uint 256) (NumV off))) actual.vs_memory =
    enc_number (Uint 256) (NumV off)` by
    (simp_tac bool_ss [LENGTH_enc_number] >>
     asm_simp_tac (srw_ss()) [abi_encoder_word_window, enc_number_def]) >>
  mp_tac (Q.INST [`mem` |-> `actual.vs_memory`] abi_encoder_tuple_prefix_append) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[Excl "enc_def"]) >> simp[]
QED

Theorem abi_scratch_array_dynamic_step:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\ is_dynamic ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ abi_footprint_disjoint d output_size fp /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame ([(d+32+j*abi_member_head_size ty,32);
    (d+32+off,LENGTH (enc ty (EL j avs)))]++fp) initial actual /\
  mem_word_at (d+32+j*abi_member_head_size ty) actual.vs_memory = n2w off /\
  mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  `j <= LENGTH avs` by decide_tac >> drule_all abi_encoder_array_prefix_sizes >> strip_tac >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  `abi_footprint_disjoint d 32 fp /\ abi_footprint_disjoint (d+32) (output_size-32) fp` by
    (conj_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `output_size`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_prefix_def]) >>
  `mload d actual = mload d initial` by
    (irule abi_decode_footprint_frame_mload >>
     qexists_tac `[(d+32+j*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL j avs)))]++fp` >>
     asm_simp_tac bool_ss [abi_footprint_disjoint_append] >>
     simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac) >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs)` by
    full_simp_tac bool_ss [mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`pre` |-> `REPLICATE j ty`, `pvs` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `heads` |-> `j*abi_member_head_size ty`,
    `tails` |-> `SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`,
    `hl` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_scratch_tuple_dynamic_step) >>
  impl_tac >- (full_simp_tac bool_ss [LENGTH_REPLICATE] >> decide_tac) >> disch_tac >>
  irule abi_encoder_array_prefix_advance >> asm_simp_tac bool_ss []
QED
