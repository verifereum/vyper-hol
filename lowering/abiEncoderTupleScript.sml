Theory abiEncoderTuple
Ancestors
  abiCanonicalWindows abiDecodeRanges abiEncoderMemory abiDecoderFrame abiDecoderContract
  valueEncoding contractABI venomState words list arithmetic

(* ===== Prefix ===== *)

(* A growing tuple encoding keeps its heads and tails in separate contiguous windows. *)

Theorem abi_encoder_memory_append:
  mem_bytes_at d (LENGTH xs) mem = xs /\
  mem_bytes_at (d+LENGTH xs) (LENGTH ys) mem = ys ==>
  mem_bytes_at d (LENGTH (xs++ys)) mem = xs++ys
Proof
  strip_tac >> PURE_REWRITE_TAC [LENGTH_APPEND, abi_encoder_mem_split] >> asm_simp_tac bool_ss []
QED

Definition abi_encoder_tuple_prefix_def:
  abi_encoder_tuple_prefix hl tys vs d mem <=>
    mem_bytes_at d (LENGTH (FLAT (abi_tuple_heads hl 0 tys vs))) mem =
      FLAT (abi_tuple_heads hl 0 tys vs) /\
    mem_bytes_at (d+hl) (LENGTH (FLAT (abi_tuple_tails tys vs))) mem =
      FLAT (abi_tuple_tails tys vs)
End

Theorem abi_encoder_tuple_prefix_empty[simp]:
  abi_encoder_tuple_prefix hl [] [] d mem
Proof
  simp[abi_encoder_tuple_prefix_def, abi_tuple_heads_def, abi_tuple_tails_def, mem_bytes_at_def]
QED

Theorem abi_encoder_tuple_prefix_parts:
  LENGTH pre = LENGTH pvs ==>
  FLAT (abi_tuple_heads hl 0 (pre++[ty]) (pvs++[av])) =
    FLAT (abi_tuple_heads hl 0 pre pvs) ++
    (if is_dynamic ty then
       enc_number (Uint 256) (NumV (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))))
     else enc ty av) /\
  FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])) =
    FLAT (abi_tuple_tails pre pvs) ++ (if is_dynamic ty then enc ty av else [])
Proof
  strip_tac >> simp[abi_tuple_heads_append, abi_tuple_tails_append, abi_tuple_heads_def,
    abi_tuple_tails_def, FLAT_APPEND, abi_tuple_tails_length]
QED

Theorem abi_encoder_tuple_prefix_append:
  LENGTH pre = LENGTH pvs /\ abi_encoder_tuple_prefix hl pre pvs d mem /\
  mem_bytes_at (d+LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)))
    (LENGTH (if is_dynamic ty then
      enc_number (Uint 256) (NumV (hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))) else enc ty av)) mem =
      (if is_dynamic ty then
        enc_number (Uint 256) (NumV (hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))) else enc ty av) /\
  mem_bytes_at (d+hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))
    (LENGTH (if is_dynamic ty then enc ty av else [])) mem =
      (if is_dynamic ty then enc ty av else []) ==>
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_encoder_tuple_prefix_parts >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_encoder_tuple_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_tuple_prefix_def]) >>
  asm_simp_tac bool_ss [abi_encoder_tuple_prefix_def, LENGTH_APPEND, abi_encoder_mem_split, ADD_ASSOC]
QED

Theorem abi_encoder_tuple_prefix_frame:
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint d (LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs))) fp /\
  abi_footprint_disjoint (d+hl) (LENGTH (FLAT (abi_tuple_tails pre pvs))) fp ==>
  abi_encoder_tuple_prefix hl pre pvs d actual.vs_memory
Proof
  simp_tac bool_ss [abi_encoder_tuple_prefix_def, abi_decode_footprint_frame_def] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_tuple_prefix_disjoint:
  heads+head_sz <= hl /\ off = hl+tails /\ off+tail_sz <= output_size /\
  (d+output_size <= b \/ b+cap <= d) ==>
  abi_footprint_disjoint d heads [(d+heads,head_sz);(d+off,tail_sz);(b,cap)] /\
  abi_footprint_disjoint (d+hl) tails [(d+heads,head_sz);(d+off,tail_sz);(b,cap)]
Proof
  strip_tac >> simp[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >> decide_tac
QED

Theorem abi_encoder_tuple_prefix_complete:
  has_types tys vs /\
  abi_encoder_tuple_prefix (head_lengths tys 0) tys vs d mem ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV vs))) mem = enc (Tuple tys) (ListV vs)
Proof
  strip_tac >>
  `enc (Tuple tys) (ListV vs) = FLAT (abi_tuple_heads (head_lengths tys 0) 0 tys vs) ++
    FLAT (abi_tuple_tails tys vs)` by simp[Once enc_def, enc_tuple_parts, LET_THM] >>
  `LENGTH (FLAT (abi_tuple_heads (head_lengths tys 0) 0 tys vs)) = head_lengths tys 0`
    by simp[abi_tuple_heads_length, head_lengths_acc] >>
  qpat_assum `abi_encoder_tuple_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_tuple_prefix_def]) >>
  qpat_assum `enc (Tuple tys) (ListV vs) = _` (fn th => PURE_REWRITE_TAC [th]) >>
  irule abi_encoder_memory_append >> asm_simp_tac bool_ss []
QED

(* ===== Step ===== *)

(* A child write extends the two-window tuple invariant while preserving earlier members. *)

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
