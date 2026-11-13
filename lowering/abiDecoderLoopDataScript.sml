(* Source-independent loop observations with a fixed effect origin. *)
Theory abiDecoderLoopData
Ancestors
  abiDecoderSiteEffect abiDecoderExecution abiDecoderContract abiDecoderReentry
  venomState venomInst valueEncoding finite_map words arithmetic pred_set

Definition Ldata_def:
  Ldata ctx fn first writes origin idx slot ip src opc base_op B sb n j s <=>
    decode_site_effect ctx fn first writes origin s /\
    FLOOKUP s.vs_allocas idx = SOME (slot,32) /\
    slot + 32 <= s.vs_alloca_next /\ slot < dimword(:256) /\
    eval_operand ip s = SOME (n2w slot) /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand base_op s = SOME (n2w B) /\
    mload slot s = n2w j /\
    abi_decode_load opc (n2w (B+sb):bytes32) s = n2w n /\
    j <= n /\ n < dimword(:256)
End

Definition Lready_def:
  Lready ctx fn first writes origin idx slot ip src opc base_op B sb n j hdr s <=>
    Ldata ctx fn first writes origin idx slot ip src opc base_op B sb n j s /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted
End

Theorem decode_site_effect_source_load:
  decode_site_effect ctx fn next V s t /\ abi_decode_source_opcode opc /\
  (opc = MLOAD ==> decode_protects V {(w2n addr,32)}) ==>
  abi_decode_load opc addr t = abi_decode_load opc addr s
Proof
  strip_tac >> Cases_on `opc = MLOAD`
  >- (simp[abi_decode_load_def] >> irule decode_site_effect_mload >> metis_tac[]) >>
  `decode_static_frame s t` by metis_tac[decode_site_effect_static] >>
  fs[decode_static_frame_def] >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  gvs[abi_decode_source_opcode_def, abi_decode_load_def, abi_decode_source_def]
QED

Theorem Ldata_child_preserved:
  Ldata ctx fn first writes origin idx slot ip src opc base_op B sb n j s /\
  decode_site_effect ctx fn child V s t /\ first <= child /\ V SUBSET writes /\
  abi_decoder_operand_live child ip /\ abi_decoder_operand_live child src /\
  abi_decoder_operand_live child base_op /\ decode_protects V {(slot,32)} /\
  abi_decode_source_opcode opc /\
  (opc = MLOAD ==> decode_protects V {(w2n (n2w (B+sb):bytes32),32)}) ==>
  Ldata ctx fn first writes origin idx slot ip src opc base_op B sb n j t
Proof
  simp_tac bool_ss [Ldata_def] >> strip_tac >>
  `decode_site_effect ctx fn first writes origin t` by
    metis_tac[decode_site_effect_fixed_origin] >>
  `FLOOKUP t.vs_allocas idx = SOME (slot,32)` by
    metis_tac[decode_site_effect_allocation] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by metis_tac[decode_site_effect_frontier] >>
  `mload slot t = mload slot s` by metis_tac[decode_site_effect_mload] >>
  `abi_decode_load opc (n2w (B+sb):bytes32) t =
   abi_decode_load opc (n2w (B+sb):bytes32) s` by
    metis_tac[decode_site_effect_source_load] >>
  rpt conj_tac >> metis_tac[decode_site_effect_live, LESS_EQ_TRANS]
QED

Theorem Lready_position_ready:
  Lready ctx fn first writes origin idx slot ip src opc base_op B sb n j hdr s ==>
  abi_decode_position_loop_ready hdr ip src opc base_op B sb (n2w slot) n j s
Proof
  simp[Lready_def, Ldata_def, abi_decode_position_loop_ready_def, w2n_n2w]
QED
