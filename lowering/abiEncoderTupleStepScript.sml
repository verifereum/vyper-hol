(* A child write extends the two-window tuple invariant while preserving earlier members. *)
Theory abiEncoderTupleStep
Ancestors
  abiEncoderTuplePrefix abiEncoderMemory abiCanonicalWindows abiDecoderFrame abiDecoderContract
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_tuple_static_step:
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+LENGTH (enc ty av) <= hl /\ hl+tails <= output_size /\
  (d+output_size <= b \/ b+cap <= d) /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decode_footprint_frame [(d+heads,LENGTH (enc ty av));(b,cap)] initial actual /\
  mem_bytes_at (d+heads) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`fp` |-> `[(d+heads,LENGTH (enc ty av));(b,cap)]`]
    abi_encoder_tuple_prefix_frame) >>
  impl_tac >- (asm_simp_tac bool_ss [] >>
    simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac) >>
  strip_tac >> mp_tac (Q.INST [`mem` |-> `actual.vs_memory`] abi_encoder_tuple_prefix_append) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[Excl "enc_def", mem_bytes_at_def]) >> simp[]
QED

Theorem abi_encoder_tuple_dynamic_step:
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+32 <= hl /\ off = hl+tails /\ off+LENGTH (enc ty av) <= output_size /\
  (d+output_size <= b \/ b+cap <= d) /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decode_footprint_frame [(d+heads,32);(d+off,LENGTH (enc ty av));(b,cap)] initial actual /\
  mem_word_at (d+heads) actual.vs_memory = n2w off /\
  mem_bytes_at (d+off) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `32`, `tail_sz` |-> `LENGTH (enc ty av)`]
    abi_encoder_tuple_prefix_disjoint) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`fp` |-> `[(d+heads,32);(d+off,LENGTH (enc ty av));(b,cap)]`]
    abi_encoder_tuple_prefix_frame) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  `mem_bytes_at (d+heads) (LENGTH (enc_number (Uint 256) (NumV off))) actual.vs_memory =
    enc_number (Uint 256) (NumV off)` by
    (simp_tac bool_ss [LENGTH_enc_number] >>
     asm_simp_tac (srw_ss()) [abi_encoder_word_window, enc_number_def]) >>
  mp_tac (Q.INST [`mem` |-> `actual.vs_memory`] abi_encoder_tuple_prefix_append) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[Excl "enc_def"]) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_TUPLE_STEP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder tuple step not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderTupleStep");
