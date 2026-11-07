(* Canonical geometry uses actual static byte lengths, not tuple cardinality. *)
Theory entryCanonicalGeometry
Ancestors
  entryCanonicalEmptyWindow abiCanonicalWindows abiDecodeRanges
  abiValidMember abiValidMembers abiCanonicalHeadSize vyperABI venomState
  contractABI words list rich_list arithmetic byte venomMemProps
Libs wordsLib

Theorem entry_geometry_head_length[local]:
  is_dynamic ty \/ LENGTH (enc ty v) = static_length ty ==>
  LENGTH (if is_dynamic ty then word_to_bytes (n2w off : 256 word) T
          else enc ty v) = abi_member_head_size ty
Proof
  Cases_on `is_dynamic ty` >> simp[abi_member_head_size_def]
QED

Theorem entry_geometry_heads_length:
  !tys vs hl tl.
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) tys vs ==>
  LENGTH (FLAT (abi_tuple_heads hl tl tys vs)) =
    SUM (MAP abi_member_head_size tys)
Proof
  Induct >> Cases_on `vs` >> simp[abi_tuple_heads_def] >>
  rpt strip_tac >> rename1 `enc ty av` >>
  `LENGTH (if is_dynamic ty then word_to_bytes (n2w (hl+tl) : 256 word) T
           else enc ty av) = abi_member_head_size ty` by
    (irule entry_geometry_head_length >> simp[]) >> simp[]
QED

Theorem entry_geometry_zero_width[local]:
  !n. LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (REPLICATE n (Tuple [])) (REPLICATE n (ListV []))
Proof
  Induct >> simp[REPLICATE, Once enc_def, enc_tuple_parts,
    abi_tuple_heads_def, abi_tuple_tails_def, static_length_def, is_dynamic_def,
    REV_DEF]
QED

Theorem entry_geometry_head_window:
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (pre ++ ty::post) (pvs ++ v::rest) /\ LENGTH pre = LENGTH pvs ==>
  let hl = head_lengths (pre ++ ty::post) 0 in
  let tl = SUM (MAP2 abi_member_tail_size pre pvs) in
  TAKE (abi_member_head_size ty)
    (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) =
    (if is_dynamic ty then enc_number (Uint 256) (NumV (hl + tl))
     else enc ty v)
Proof
  strip_tac >>
  `LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) pre pvs /\
   (~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) /\
   LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) post rest` by
    gvs[LIST_REL_APPEND_EQ] >>
  simp_tac bool_ss [LET_THM] >> irule abi_window_from_parts >>
  conj_tac >- (Cases_on `is_dynamic ty` >>
    gvs[abi_member_head_size_def, enc_number_def]) >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs)`,
     `FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
       (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
       post rest) ++ FLAT (abi_tuple_tails pre pvs) ++
       (if is_dynamic ty then enc ty v else []) ++
       FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      match_mp_tac (SIMP_RULE pureSimps.pure_ss [LET_THM] canonical_member_parts) >>
      first_assum ACCEPT_TAC) >>
  simp[entry_geometry_heads_length]
QED

Theorem entry_geometry_tail_window:
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty ==>
  TAKE (LENGTH (enc ty v))
    (DROP (head_lengths (pre ++ ty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)))) = enc ty v
Proof
  strip_tac >>
  `LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) pre pvs /\
   LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) post rest` by
    gvs[LIST_REL_APPEND_EQ] >>
  `LENGTH post = LENGTH rest` by metis_tac[LIST_REL_LENGTH] >>
  irule abi_window_from_parts >> conj_tac >- REFL_TAC >>
  qexistsl_tac
    [`FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0) 0 pre pvs) ++
      enc_number (Uint 256)
        (NumV (head_lengths (pre ++ ty::post) 0 +
               SUM (MAP2 abi_member_tail_size pre pvs))) ++
      FLAT (abi_tuple_heads (head_lengths (pre ++ ty::post) 0)
        (SUM (MAP2 abi_member_tail_size pre pvs) + abi_member_tail_size ty v)
        post rest) ++ FLAT (abi_tuple_tails pre pvs)`,
     `FLAT (abi_tuple_tails post rest)`] >>
  conj_tac
  >- (pure_rewrite_tac[APPEND_ASSOC] >>
      qpat_x_assum `is_dynamic ty` (fn dyn =>
        match_mp_tac (SIMP_RULE bool_ss [LET_THM,dyn] canonical_member_parts)) >>
      first_assum ACCEPT_TAC) >>
  simp[entry_geometry_heads_length, abi_tuple_tails_length,
       head_lengths_acc, MAP_APPEND, SUM_APPEND, abi_member_head_size_def] >>
  decide_tac
QED

Theorem entry_geometry_ranges:
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (pre ++ ty::post) (pvs ++ v::rest) /\ LENGTH pre = LENGTH pvs ==>
  let totlen = LENGTH (enc (Tuple (pre ++ ty::post))
                            (ListV (pvs ++ v::rest))) in
  let head = SUM (MAP abi_member_head_size pre) in
  let tail = SUM (MAP abi_member_head_size (pre ++ ty::post)) +
             SUM (MAP2 abi_member_tail_size pre pvs) in
    head + abi_member_head_size ty <= totlen /\
    (is_dynamic ty ==> tail + LENGTH (enc ty v) <= totlen) /\
    (~is_dynamic ty ==> head + LENGTH (enc ty v) <= totlen)
Proof
  strip_tac >>
  `LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) pre pvs /\
   (~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) /\
   LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t) post rest` by
    gvs[LIST_REL_APPEND_EQ] >>
  `LENGTH post = LENGTH rest` by metis_tac[LIST_REL_LENGTH] >>
  Cases_on `is_dynamic ty` >>
  simp[Once enc_def, enc_tuple_parts, REV_DEF,
    entry_geometry_heads_length, abi_tuple_tails_length, enc_number_def,
    abi_tuple_heads_append, abi_tuple_tails_append,
    abi_tuple_heads_def, abi_tuple_tails_def,
    head_lengths_acc, MAP_APPEND, SUM_APPEND, abi_member_head_size_def] >>
  decide_tac
QED

Theorem entry_geometry_dynamic_offset[local]:
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (pre ++ at::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic at /\
  LENGTH (enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest))) < dimword (:256) ==>
  abi_decode_member_offset at
    (enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest)))
    (SUM (MAP abi_member_head_size pre)) =
  head_lengths (pre ++ at::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)
Proof
  strip_tac >> drule_all entry_geometry_head_window >>
  simp_tac bool_ss [LET_THM, abi_member_head_size_def] >> strip_tac >>
  drule_all entry_geometry_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
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

Theorem entry_geometry_dynamic_bound[local]:
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (pre ++ at::post) (pvs ++ v::rest) /\
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
  drule_all entry_geometry_dynamic_offset >> strip_tac >>
  drule_all entry_geometry_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  conj_tac >- (gvs[head_lengths_acc] >> decide_tac) >>
  conj_tac >- simp[abi_decode_member_bytes_def, abi_decode_member_offset_def] >>
  simp[LENGTH_DROP] >> gvs[head_lengths_acc] >> decide_tac
QED

Theorem entry_geometry_dynamic_window:
  LIST_REL (\t v. is_dynamic t \/ LENGTH (enc t v) = static_length t)
    (pre ++ at::post) (pvs ++ v::rest) /\
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
  drule_all entry_geometry_dynamic_bound >>
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
  drule_all entry_geometry_dynamic_offset >> strip_tac >>
  drule_all entry_geometry_head_window >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def, enc_number_def] >>
  strip_tac >>
  drule_all entry_geometry_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `SUM (MAP abi_member_head_size pre) + 32 <=
    LENGTH (enc (Tuple (pre ++ at::post)) (ListV (pvs ++ v::rest)))` by
    gvs[abi_member_head_size_def] >>
  `sb + SUM (MAP abi_member_head_size pre) < dimword (:256)` by decide_tac >>
  drule_all abi_decode_load_window >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "canonical geometry inherited admission"
  end)
  [entry_geometry_head_length, entry_geometry_heads_length,
   entry_geometry_zero_width, entry_geometry_head_window,
   entry_geometry_tail_window, entry_geometry_ranges,
   entry_geometry_dynamic_offset, entry_geometry_dynamic_bound,
   entry_geometry_dynamic_window];
