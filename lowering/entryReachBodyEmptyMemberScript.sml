(* The zero-sized dynamic descriptor follows its inline head, not an offset. *)
Theory entryReachBodyEmptyMember
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyMemberSetup abiDecoderEmpty abiDecoderOffset abiDecoderDynamic
  abiDecoderCoherence abiDecoderComplexHead abiDecoderContract
  abiEncoder compileEnv valueEncoding words list arithmetic

Theorem entry_empty_member_decoder[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecComplex T []) st = ((),last) ==> last = st
Proof
  simp[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def,
       comp_return_def]
QED

Theorem entry_empty_dynamic_member_endpoint:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decoder_metadata ce env ty tv ei av v /\
  ei = type_to_abi_dec_info ce.ce_struct_fields ce ty /\ ei = DecComplex T [] /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset ei) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    ei mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ val_in_memory tv v (d+vo) u.vs_memory /\
    type_memory_size tv = 0 /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w (sb+ao)) /\
    eval_operand (SND ops) u = SOME (n2w (d+vo)) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = last.cs_current_bb /\
    u.vs_inst_idx = LENGTH last.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `last = mid` by metis_tac[entry_empty_member_decoder] >> gvs[] >>
  `~dec_info_needs_offset (DecComplex T [])` by
    simp[abi_decoder_needs_offset_iff] >>
  `type_memory_bytes ce ty = 0 /\ !d mem. val_in_memory tv v d mem` by
    (irule abi_decoder_empty_metadata_value >> metis_tac[]) >>
  `type_memory_size tv = 0` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  mp_tac (Q.INST [`dyn` |-> `F`, `mid` |-> `last`] entry_member_setup_endpoint) >>
  simp_tac bool_ss [] >> impl_tac >- asm_rewrite_tac[] >>
  simp[ADD_COMM] >> metis_tac[]
QED

Theorem entry_nonempty_member_offset:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty <> DecComplex T [] ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  metis_tac[abi_decoder_nonempty_offset, abi_decoder_coherent_dynamic]
QED
