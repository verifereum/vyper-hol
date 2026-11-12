(* Successful source-backed member navigation over owned allocations. *)
Theory abiValidAllocatedNavigate
Ancestors
  abiValidAllocatedSource abiValidAllocatedMemberSetup abiMalformedMemberSetup
  abiDecoderMemberSetup abiDecoderOffset abiDecoderOffsetHead abiDecoderCoherence
  abiMalformedRecursiveInterface abiDecoderContract abiDecodeRanges
  abiEncoder compileEnv venomState words list arithmetic vyperABI contractABI
  abiDecoderDynamic abiMalformedNavigation

Theorem abi_valid_allocated_member_navigate:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  LENGTH xs = L /\
  p+ao+abi_member_head_size (vyper_to_abi_type env ty) <= L /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs)) /\
  vo+type_memory_bytes ce ty <= outsz /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_entry ctx func cenv cx es en sites dstid live
      base_op hi (FST ops) (SND ops) B L xs
      (p + if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
           then abi_head_word (DROP (p+ao) xs) else ao)
      (d+vo) (type_memory_bytes ce ty) t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t
Proof
  strip_tac >>
  `p + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
        then abi_head_word (DROP (p+ao) xs) else ao) <= L` by
    (metis_tac[abi_valid_source_member_position]) >>
  `hi <> Lit 0w /\ p < dimword (:256) /\ L < dimword (:256) /\
   B+L < dimword (:256) /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs /\
   eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
   eval_operand base_op s = SOME (n2w B) /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op]` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_decode_source_def] >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) ==>
   p+ao+32 <= L` by
    (drule abi_decoder_coherent_dynamic >> strip_tac >>
     fs[abi_decoder_needs_offset_iff, abi_member_head_size_def] >>
     Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []` >> gvs[] >>
     strip_tac >> gvs[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) ==>
   abi_decode_load MLOAD (n2w (B+(p+ao)):bytes32) s =
     n2w (abi_head_word (DROP (p+ao) xs))` by
    (metis_tac[abi_checked_offset_load]) >>
  drule abi_decode_member_setup_reentry >>
  disch_then (drule_at (Pat `eval_operand src s = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst s = _`)) >>
  disch_then (qspecl_then [`abi_head_word (DROP (p+ao) xs)`, `ceiling`, `B`] mp_tac) >>
  (impl_tac >- (simp[abi_decode_source_opcode_def] >> fs[EVERY_DEF] >>
    strip_tac >> gvs[] >> decide_tac)) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  irule abi_malformed_member_setup_entry >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
    fs[AC ADD_ASSOC ADD_COMM] >> decide_tac) >> metis_tac[]
QED
