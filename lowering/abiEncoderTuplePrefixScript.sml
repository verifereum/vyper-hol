(* A growing tuple encoding keeps its heads and tails in separate contiguous windows. *)
Theory abiEncoderTuplePrefix
Ancestors
  abiCanonicalWindows abiDecodeRanges abiEncoderMemory abiDecoderFrame abiDecoderContract
  valueEncoding contractABI venomState words list arithmetic

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_TUPLE_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder tuple prefix not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderTuplePrefix");
