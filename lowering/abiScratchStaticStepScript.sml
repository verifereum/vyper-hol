(* A static child extends the output prefix while preserving physical scratch.
   TOP-LEVEL: abi_scratch_array_static_step advances the count/head invariant.
   Helpers: single-head write separation and tuple prefix extension. *)
Theory abiScratchStaticStep
Ancestors
  abiScratchFootprint abiEncoderArrayFrame abiEncoderArrayBounds abiEncoderArrayPrefix abiEncoderArrayLayout
  abiEncoderTuplePrefix abiEncoderMemory abiCanonicalWindows abiDecoderFrame abiDecoderContract
  valueEncodingProps valueEncoding contractABI venomState words list rich_list arithmetic

Theorem abi_scratch_static_prefix_windows:
  heads+head_sz <= hl /\ hl+tails <= output_size /\ abi_footprint_disjoint d output_size fp ==>
  abi_footprint_disjoint d heads ((d+heads,head_sz)::fp) /\
  abi_footprint_disjoint (d+hl) tails ((d+heads,head_sz)::fp)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint d heads fp /\ abi_footprint_disjoint (d+hl) tails fp` by
    (conj_tac >> irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `output_size`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_disjoint_cons] >> decide_tac
QED

Theorem abi_scratch_tuple_static_step:
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+LENGTH (enc ty av) <= hl /\ hl+tails <= output_size /\
  abi_footprint_disjoint d output_size fp /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decode_footprint_frame ((d+heads,LENGTH (enc ty av))::fp) initial actual /\
  mem_bytes_at (d+heads) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `LENGTH (enc ty av)`] abi_scratch_static_prefix_windows) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`fp` |-> `(d+heads,LENGTH (enc ty av))::fp`] abi_encoder_tuple_prefix_frame) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  mp_tac (Q.INST [`mem` |-> `actual.vs_memory`] abi_encoder_tuple_prefix_append) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[Excl "enc_def", mem_bytes_at_def]) >> simp[]
QED

Theorem abi_scratch_array_static_step:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\ ~is_dynamic ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ abi_footprint_disjoint d output_size fp /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame ((d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))::fp) initial actual /\
  mem_bytes_at (d+32+j*abi_member_head_size ty) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) ==>
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
     qexists_tac `(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))::fp` >>
     asm_simp_tac (srw_ss()) [abi_scratch_disjoint_cons] >> decide_tac) >>
  `mem_word_at d actual.vs_memory = n2w (LENGTH avs)` by full_simp_tac bool_ss [mem_word_at_eq_mload] >>
  mp_tac (Q.INST [`pre` |-> `REPLICATE j ty`, `pvs` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `heads` |-> `j*abi_member_head_size ty`,
    `tails` |-> `SUM (MAP (abi_member_tail_size ty) (TAKE j (avs:abi_value list)))`,
    `hl` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_scratch_tuple_static_step) >>
  impl_tac >- (full_simp_tac bool_ss [LENGTH_REPLICATE] >> decide_tac) >> disch_tac >>
  irule abi_encoder_array_prefix_advance >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_STATIC_STEP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch static output step not kernel closed: " ^ n)
  end) (DB.thms "abiScratchStaticStep");
