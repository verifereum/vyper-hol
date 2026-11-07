Theory entryReachBodyRegistrationWindows
Ancestors
  entryReachBodySourceWindows entryReachBodyMemberInputs
  abiDecoderMemberSlice abiDecoderContract abiCanonicalWindows abiDecodeRanges
  abiEncoderOpenInput contractABI vyperABI vyperValue venomState words
  list rich_list arithmetic abiCanonicalHeadSize byte

Theorem registration_dynamic_offset_load[local]:
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME (pvs ++ av::rest) /\
  MAP (vyper_to_abi_type env) tys = pre ++ ty::post /\ LENGTH pre = LENGTH pvs /\
  is_dynamic ty /\
  E = enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH E) (abi_decode_source CALLDATALOAD s) = E /\
  4 + LENGTH E < dimword (:256) ==>
  abi_decode_load CALLDATALOAD
    (n2w (4+SUM (MAP abi_member_head_size pre)):bytes32) s =
  n2w (head_lengths (pre ++ ty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all entry_source_member_head_window >>
  simp_tac bool_ss [LET_THM] >>
  asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `TAKE 32 (DROP ao bs)` >>
  `ao+32 <= LENGTH bs` by
    (qpat_x_assum `TAKE 32 _ = _` (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
     simp_tac (srw_ss()) [LENGTH_TAKE_EQ, LENGTH_DROP, enc_number_def,
                        LENGTH_word_to_bytes] >> decide_tac) >>
  `4+ao < dimword (:256)` by (qpat_x_assum `E = bs` SUBST_ALL_TAC >> decide_tac) >>
  qpat_x_assum `E = bs` SUBST_ALL_TAC >>
  drule_all abi_decode_load_window >>
  disch_then (qspecl_then [`s`, `CALLDATALOAD`] mp_tac) >>
  asm_simp_tac bool_ss [Abbr `bs`, Abbr `ao`] >>
  disch_then SUBST1_TAC >> asm_rewrite_tac[enc_number_def] >>
  irule word_of_bytes_word_to_bytes >> simp[dividesTheory.divides_def]
QED

Theorem registration_literal_source_window:
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME (pvs ++ av::rest) /\
  MAP (vyper_to_abi_type env) tys = pre ++ ty::post /\ LENGTH pre = LENGTH pvs /\
  E = enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH E) (abi_decode_source CALLDATALOAD s) = E /\
  4 + LENGTH E < dimword (:256) /\
  off = 4 + SUM (MAP abi_member_head_size pre) /\
  (dyn /\ ~prim <=> is_dynamic ty) ==>
  ?sb.
    (n2w sb:bytes32) =
      (if dyn /\ ~prim then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    mem_bytes_at sb (LENGTH (enc ty av)) (abi_decode_source CALLDATALOAD s) = enc ty av /\
    sb + LENGTH (enc ty av) < dimword (:256)
Proof
  strip_tac >>
  qabbrev_tac `co = abi_tuple_child_offset (pre ++ ty::post)
    (pvs ++ av::rest) (LENGTH pre)` >>
  `co = if is_dynamic ty then head_lengths (pre ++ ty::post) 0 +
       SUM (MAP2 abi_member_tail_size pre pvs)
     else SUM (MAP abi_member_head_size pre)` by
    simp[Abbr `co`, abi_tuple_child_offset_append, TAKE_LENGTH_APPEND] >>
  `mem_bytes_at (4+co) (LENGTH (enc ty av)) (abi_decode_source CALLDATALOAD s) = enc ty av /\
   4+co+LENGTH (enc ty av) < dimword (:256)` by
    (irule entry_source_member_source >> goal_assum (drule_at Any) >>
     qexistsl_tac [`E`, `env`, `rest`, `tys`, `vs`] >> asm_rewrite_tac[]) >>
  qexists_tac `4+co` >> reverse conj_tac >- asm_rewrite_tac[] >>
  `off-4 = SUM (MAP abi_member_head_size pre)` by decide_tac >>
  Cases_on `is_dynamic ty`
  >- (drule_all registration_dynamic_offset_load >>
      asm_rewrite_tac[GSYM word_add_n2w] >> strip_tac >> metis_tac[]) >>
  asm_rewrite_tac[word_add_n2w]
QED
