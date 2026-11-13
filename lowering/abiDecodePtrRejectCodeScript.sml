Theory abiDecodePtrRejectCode
Ancestors
  abiDecodePtrFlatLayout abiDecodePtrMemberInterface abiDecodePtrSelectedMember
  abiDecoderVarSequence abiDecoderReentryPointer abiDecoderBytesFrame abiDecoderRange abiDecoderContract
  abiDecoderComposition abiDecoderAppend abiEncoder exprLoweringProps emitHelperProps
  compileEnv emitHelper venomInst words list arithmetic

Theorem abi_decode_flat_member_reentry_code:
  abi_decode_member_code dst pos src hi ei off q sa sb /\
  abi_decode_member_layout ei off q k z h cap ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_member_code _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[abi_decode_member_code_def] >> strip_tac >>
  drule_all abi_decode_member_phase_shape >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sm sn)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, abi_decoder_reentry_opcode_def]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sn sb)` by
    (fs[abi_decode_member_layout_def] >>
     metis_tac[abi_decoder_word_reentry_code, abi_decoder_bytes_reentry_code]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sn ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  simp[]
QED

Theorem abi_decode_flat_reentry_code:
  !elems off q sa sb.
    abi_decode_flat_layout elems off q z h cap /\
    compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
      elems off q sa = ((),sb) ==>
    EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)
Proof
  Induct
  >- simp[Once compile_abi_decode_to_buf_def, comp_return_def, emitted_insts_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >> strip_tac >>
  fs[abi_decode_flat_layout_def] >>
  drule abi_decode_flat_compile_cons >> strip_tac >>
  drule_all abi_decode_flat_member_shape >> strip_tac >>
  drule_all abi_decode_flat_member_reentry_code >> strip_tac >>
  fs[ADD_COMM] >>
  drule_all abi_decode_flat_compile_shape >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sm sb)` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[ADD_COMM]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[]
QED
