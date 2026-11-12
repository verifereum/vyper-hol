(* Canonical full-tuple offsets remain bounded for empty dynamic members. *)
Theory entryCanonicalEmptyWindow
Ancestors
  abiValidMember abiValidMembers abiCanonicalHeadSize abiCanonicalWindows abiDecodeRanges
  vyperABI contractABI venomState words list arithmetic byte venomMemProps
Libs wordsLib

Theorem entry_canonical_dynamic_member_offset:
  has_types (pre ++ at::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic at /\
  LENGTH (enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest))) < dimword (:256) ==>
  abi_decode_member_offset at
    (enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest)))
    (SUM (MAP abi_member_head_size pre)) =
  head_lengths (pre ++ at::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)
Proof
  strip_tac >> drule_all canonical_member_head_window >>
  simp_tac bool_ss [LET_THM, abi_member_head_size_def] >> strip_tac >>
  drule_all canonical_member_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `head_lengths (pre ++ at::post) 0 +
    SUM (MAP2 abi_member_tail_size pre pvs) < dimword (:256)` by
    (gvs[head_lengths_acc] >> decide_tac) >>
  qpat_x_assum `TAKE _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_member_offset_def, abi_head_word_def,
    dec_number_def, dest_NumV_def, enc_number_def] >>
  simp[word_of_bytes_word_to_bytes, w2n_n2w] >>
  gvs[dimword_def] >> decide_tac
QED

(* A dynamic member slice includes all later tails, even for an empty member. *)
Theorem entry_empty_member_slice_not_empty:
  let at = Array (SOME 0) (Bytes NONE) in
  let bs = enc (Tuple [at; Bytes NONE]) (ListV [ListV []; BytesV []]) in
  abi_decode_member_bytes at bs bs <> []
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC >> EVAL_TAC
QED

Theorem entry_canonical_dynamic_member_bound:
  has_types (pre ++ at::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic at /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest)) /\
  LENGTH bs < dimword (:256) ==>
  let ao = SUM (MAP abi_member_head_size pre);
      k = abi_decode_member_offset at bs ao in
  k <= LENGTH bs /\
  abi_decode_member_bytes at bs (DROP ao bs) = DROP k bs /\
  k + LENGTH (DROP k bs) = LENGTH bs
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> qpat_x_assum `bs = _` SUBST_ALL_TAC >>
  drule_all entry_canonical_dynamic_member_offset >> strip_tac >>
  drule_all canonical_member_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  conj_tac >- (gvs[head_lengths_acc] >> decide_tac) >>
  conj_tac >- simp[abi_decode_member_bytes_def, abi_decode_member_offset_def] >>
  simp[LENGTH_DROP] >> gvs[head_lengths_acc] >> decide_tac
QED

Theorem entry_canonical_dynamic_member_window:
  has_types (pre ++ at::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic at /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest)) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  let ao = SUM (MAP abi_member_head_size pre);
      k = abi_decode_member_offset at bs ao in
  k <= LENGTH bs /\
  abi_decode_member_bytes at bs (DROP ao bs) = DROP k bs /\
  k + LENGTH (DROP k bs) = LENGTH bs /\
  sb + k < dimword (:256) /\
  mem_bytes_at (sb+k) (LENGTH (DROP k bs)) (abi_decode_source opc s) = DROP k bs /\
  abi_decode_load opc (n2w (sb+ao):256 word) s = n2w k
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  drule_all entry_canonical_dynamic_member_bound >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `sb + abi_decode_member_offset at bs (SUM (MAP abi_member_head_size pre)) <
    dimword (:256)` by decide_tac >>
  `mem_bytes_at (sb + abi_decode_member_offset at bs (SUM (MAP abi_member_head_size pre)))
    (LENGTH (DROP (abi_decode_member_offset at bs (SUM (MAP abi_member_head_size pre))) bs))
    (abi_decode_source opc s) =
    DROP (abi_decode_member_offset at bs (SUM (MAP abi_member_head_size pre))) bs` by
    (irule EQ_TRANS >> irule_at Any abi_decode_source_window >>
     qexists_tac `bs` >> asm_rewrite_tac[LESS_EQ_REFL] >> simp_tac (srw_ss()) [TAKE_LENGTH_ID_rwt]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `bs = _` SUBST_ALL_TAC >>
  drule_all entry_canonical_dynamic_member_offset >> strip_tac >>
  asm_rewrite_tac[] >> irule canonical_member_offset_load >>
  asm_rewrite_tac[] >> qexistsl_tac [`rest`, `v`] >> asm_rewrite_tac[]
QED

(* Zero fixed arrays require no bytes; a canonical member suffix can contain
   later members' tails without invalidating this check. *)
Theorem entry_fixed_zero_array_suffix_valid:
  vyper_decode_valid_enc (Array (SOME 0) elem) bs
Proof
  simp[vyper_decode_valid_enc_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry canonical window inherited admission"
  end)
  [entry_canonical_dynamic_member_offset, entry_empty_member_slice_not_empty,
   entry_canonical_dynamic_member_bound, entry_canonical_dynamic_member_window,
   entry_fixed_zero_array_suffix_valid];
