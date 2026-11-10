Theory abiDecodePtrRejectValidMember
Ancestors
  abiDecodePtrRejectCapacity abiDecodePtrRejectSource abiValidMember
  abiDecoderValidArray abiDecoderMembers abiDecoderContract abiDecoderRange
  abiDecodePtrMemberInterface exprLowering
  vyperABI contractABI abiEncoder compileEnv venomState venomExecSemantics words list arithmetic

Theorem abi_decode_valid_bytes_member_reject_inputs:
  (at = Bytes NONE \/ at = String) /\
  vyper_decode_valid_enc_tuple (pre ++ at::post) bs bs /\
  dec at (abi_decode_member_bytes at bs
    (DROP (SUM (MAP abi_member_head_size pre)) bs)) = contractABI$BytesV payload /\
  n < LENGTH payload /\
  mem_bytes_at B (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B + LENGTH bs < dimword(:256) ==>
  let off = SUM (MAP abi_member_head_size pre);
      delta = abi_decode_member_offset at bs off in
  abi_decode_load MLOAD (n2w (B+off) : bytes32) s = n2w delta /\
  delta + 32 <= LENGTH bs /\
  n < w2n (abi_decode_load MLOAD (n2w (B+delta) : bytes32) s)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `is_dynamic at /\ (!elem. at <> Array (SOME 0) elem)` by
    (Cases_on `at = Bytes NONE` >> gvs[] >> simp[is_dynamic_def]) >>
  drule abi_valid_member_window >>
  disch_then (qspecl_then [`B`, `s`, `MLOAD`] mp_tac) >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `vyper_decode_valid_enc at data` >>
  `32 <= LENGTH data /\ abi_head_word data = LENGTH payload` by
    (gvs[vyper_decode_valid_enc_def, dec_def, dec_number_def, dest_NumV_def,
      abi_head_word_def, LET_THM, LENGTH_TAKE]) >>
  `B + abi_decode_member_offset at bs (SUM (MAP abi_member_head_size pre)) +
    LENGTH data < dimword(:256)` by decide_tac >>
  drule_all abi_decoder_source_head_load >> strip_tac >>
  `LENGTH payload < dimword(:256)` by
    (gvs[abi_head_word_def] >> metis_tac[w2n_lt]) >>
  simp[] >> decide_tac
QED

Theorem abi_decode_selected_valid_bytes_reject:
  (ty = BaseT (StringT n) \/ ty = BaseT (BytesT (Dynamic n))) /\
  abi_decode_member_code dst (Lit 0w) src hi
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (SUM (MAP abi_member_head_size pre)) q sa sb /\
  vyper_decode_valid_enc_tuple (pre ++ vyper_to_abi_type env ty::post) bs bs /\
  dec (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)) = contractABI$BytesV payload /\
  n < LENGTH payload /\ n < dimword(:256) /\
  mem_bytes_at B (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B + LENGTH bs < dimword(:256) /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand (Var dst) s = SOME d /\
  eval_operand hi s = SOME (n2w (LENGTH bs)) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s ==>
  ?u. abi_decode_reject_witness (emitted_insts sa sb) s u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN ``vyper_to_abi_type env ty = Bytes NONE \/ vyper_to_abi_type env ty = String`` assume_tac
  >- (Cases_on `ty = BaseT (StringT n)` >>
      gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def]) >>
  `type_to_abi_dec_info ce.ce_struct_fields ce ty = DecBytestring n` by
    (Cases_on `ty = BaseT (StringT n)` >> gvs[type_to_abi_dec_info_def]) >>
  drule_all abi_decode_valid_bytes_member_reject_inputs >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  irule abi_decode_selected_bytes_capacity_reject_witness >> asm_simp_tac bool_ss [] >>
  goal_assum (drule_at (Pat `abi_decode_member_code _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`B`, `d`, `abi_decode_member_offset
    (vyper_to_abi_type env ty) bs (SUM (MAP abi_member_head_size pre))`, `LENGTH bs`, `0`] >>
  simp[eval_operand_def] >> decide_tac
QED
