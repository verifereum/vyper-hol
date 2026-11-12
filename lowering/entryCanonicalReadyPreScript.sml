(* Canonical full-tuple windows at an already chosen registration state. *)
Theory entryCanonicalReadyPre
Ancestors
  entryCanonicalEmptyWindow entryRegistrationSourceWindow entryZeroReservePre
  abiValidDecodedMetadata abiValidMember abiValidMembers abiCanonicalWindows abiDecodeRanges
  vyperABIValid contractABI vyperABI compileEnv venomState words list arithmetic

Theorem entry_canonical_tuple_valid[local]:
  has_types ats avs /\ bs = enc (Tuple ats) (ListV avs) /\
  LENGTH bs < dimword (:256) ==>
  vyper_decode_valid_enc_tuple ats bs bs
Proof
  strip_tac >> gvs[Once enc_def] >>
  qspecl_then [`head_lengths ats 0`, `0`, `ats`, `avs`, `[]`, `[]`, `[]`]
    mp_tac (cj 2 enc_valid) >>
  asm_simp_tac (srw_ss()) [Once enc_def, LET_THM] >>
  metis_tac[cj 3 valid_enc_vyper_decode_valid_enc_mutual]
QED

Theorem entry_canonical_member_window:
  has_types (pre ++ at::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD ready) = bs /\
  4 + LENGTH bs < dimword (:256) ==>
  let ao = SUM (MAP abi_member_head_size pre);
      k = abi_decode_member_offset at bs ao;
      bytes = abi_decode_member_bytes at bs (DROP ao bs) in
  vyper_decode_valid_enc at bytes /\
  (is_dynamic at \/ static_length at <= LENGTH bytes) /\
  k + LENGTH bytes <= LENGTH bs /\
  4 + k < dimword (:256) /\
  mem_bytes_at (4+k) (LENGTH bytes) (abi_decode_source CALLDATALOAD ready) = bytes /\
  (is_dynamic at ==> abi_decode_load CALLDATALOAD (n2w (4+ao):bytes32) ready = n2w k)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  drule_all entry_canonical_tuple_valid >> strip_tac >>
  drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic at`
  >- (drule_all entry_canonical_dynamic_member_window >>
      simp_tac bool_ss [LET_THM] >> strip_tac >>
      qpat_x_assum `bs = enc _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
      asm_simp_tac bool_ss [] >> decide_tac) >>
  `SUM (MAP abi_member_head_size pre) + static_length at <= LENGTH bs` by
    (qpat_x_assum `_ + abi_member_head_size at <= _` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  drule_all abi_valid_static_member_window >> strip_tac >>
  qpat_x_assum `bs = enc _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `static_length at <= LENGTH (DROP (SUM (MAP abi_member_head_size pre)) bs)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_decode_member_offset_def] >>
  simp[abi_decode_member_bytes_def, LENGTH_TAKE_EQ]
QED
