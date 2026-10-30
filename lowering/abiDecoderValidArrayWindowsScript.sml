(* Actual dynamic-array child windows, including arbitrary source head offsets. *)
Theory abiDecoderValidArrayWindows
Ancestors
  abiValidMembers abiValidAggregateHeads abiValidMember abiDecoderValidMemberInput
  abiCanonicalArrayLoad abiDecodeRanges abiDecoderContract valueEncoding vyperABI contractABI
  venomState words list rich_list arithmetic

Theorem abi_decoder_replicate_member:
  !n j at. j < n ==>
    REPLICATE n at = REPLICATE j at ++ at::REPLICATE (n - SUC j) at
Proof
  rpt strip_tac >> simp_tac bool_ss [GSYM REPLICATE, REPLICATE_APPEND] >>
  `j + SUC (n - SUC j) = n` by decide_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_array_payload_window:
  vyper_decode_valid_enc (Array NONE at) bs /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  32 <= LENGTH bs /\
  vyper_decode_valid_enc_tuple (REPLICATE (abi_head_word bs) at) (DROP 32 bs) (DROP 32 bs) /\
  mem_bytes_at (sb + 32) (LENGTH (DROP 32 bs)) (abi_decode_source opc s) = DROP 32 bs /\
  sb + 32 + LENGTH (DROP 32 bs) < dimword (:256)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  `32 + LENGTH (DROP 32 bs) = LENGTH bs` by (simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac bool_ss [GSYM ADD_ASSOC] >>
  mp_tac (Q.INST [`off` |-> `32:num`, `n` |-> `LENGTH (DROP 32 (bs:word8 list))`]
    abi_decode_source_window) >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_valid_array_child_window:
  vyper_decode_valid_enc (Array NONE at) bs /\ j < abi_head_word bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  let payload = DROP 32 bs;
      ao = j * abi_member_head_size at;
      off = 32 + abi_decode_member_offset at payload ao;
      data = abi_decode_member_bytes at payload (DROP ao payload) in
  vyper_decode_valid_enc at data /\ abi_member_head_size at <= LENGTH data /\
  off + LENGTH data <= LENGTH bs /\ sb + off < dimword (:256) /\
  mem_bytes_at (sb + off) (LENGTH data) (abi_decode_source opc s) = data /\
  (is_dynamic at ==> abi_decode_load opc (n2w (sb + 32 + ao):bytes32) s = n2w (off - 32))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_array_payload_window >> strip_tac >>
  mp_tac (Q.ISPECL [`abi_head_word (bs:word8 list)`, `j:num`, `at:abi_type`]
    abi_decoder_replicate_member) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `REPLICATE (abi_head_word bs) at = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM, map_replicate, SUM_REPLICATE]
    (Q.INST [`bs` |-> `DROP 32 (bs:word8 list)`, `sb` |-> `sb + 32`,
      `pre` |-> `REPLICATE j at`, `ats` |-> `REPLICATE (abi_head_word bs - SUC j) at`]
      abi_valid_member_window)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]) >>
  asm_simp_tac arith_ss [GSYM ADD_ASSOC] >>
  fs[LENGTH_DROP, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >> decide_tac
QED
