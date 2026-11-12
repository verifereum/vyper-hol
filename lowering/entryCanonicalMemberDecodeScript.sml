(* Canonical member decoding retains arbitrary later tuple tails. *)
Theory entryCanonicalMemberDecode
Ancestors
  entryCanonicalEmptyWindow abiCanonicalWindows abiValidMembers contractABI
  vyperABI abiCanonicalHeadSize abiValidMember abiDecodeRanges words list arithmetic

Theorem entry_decode_encoded_prefix[local]:
  has_type at av /\ LENGTH bs < dimword (:256) /\
  TAKE (LENGTH (enc at av)) bs = enc at av ==>
  dec at bs = av
Proof
  strip_tac >>
  `LENGTH (enc at av) <= LENGTH bs` by
    (qpat_x_assum `TAKE _ _ = _` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
     simp[LENGTH_TAKE_EQ]) >>
  `LENGTH (enc at av) < dimword (:256)` by decide_tac >>
  drule_all (cj 1 dec_enc) >>
  disch_then (qspec_then `DROP (LENGTH (enc at av)) bs` mp_tac) >>
  metis_tac[TAKE_DROP]
QED

Theorem entry_canonical_member_decode:
  has_types (pre ++ at::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest)) /\
  4 + LENGTH bs < dimword (:256) ==>
  dec at (abi_decode_member_bytes at bs
    (DROP (SUM (MAP abi_member_head_size pre)) bs)) = av
Proof
  strip_tac >>
  `has_type at av` by gvs[has_types_append, has_type_def] >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  qpat_x_assum `bs = _` SUBST_ALL_TAC >>
  Cases_on `is_dynamic at`
  >- (drule_all entry_canonical_dynamic_member_offset >> strip_tac >>
      drule_all canonical_member_tail_window >> strip_tac >>
      irule entry_decode_encoded_prefix >>
      asm_simp_tac bool_ss [abi_decode_member_bytes_def, LET_THM] >>
      conj_tac >- (simp_tac bool_ss [LENGTH_DROP] >> decide_tac) >>
      qpat_x_assum `abi_decode_member_offset _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [abi_decode_member_offset_def, COND_CLAUSES] >>
      disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all canonical_member_head_window >>
  asm_simp_tac bool_ss [LET_THM, abi_member_head_size_def, COND_CLAUSES] >> strip_tac >>
  `LENGTH (enc at av) = static_length at` by
    (irule (cj 1 enc_has_static_length) >> simp[]) >>
  `static_length at <= LENGTH (DROP (SUM (MAP abi_member_head_size pre))
      (enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest))))` by
    (qpat_x_assum `TAKE _ _ = _` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
     asm_simp_tac bool_ss [LENGTH_TAKE_EQ] >> decide_tac) >>
  `LENGTH (enc at av) < dimword (:256)` by
    (qpat_x_assum `static_length at <= _` mp_tac >>
     simp_tac bool_ss [LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_decode_member_bytes_def, COND_CLAUSES] >>
  drule_all (cj 1 dec_enc) >> disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
