(* Source-valid setup for static array elements, including clamped aggregates. *)
Theory calldataStaticChildSetup
Ancestors
  abiDecoderValidArrayEntry abiDecoderValidArraySetupInputs abiDecoderStaticLoopSetup
  abiDecoderCoherence abiDecoderDynamic abiDecoderOffset abiDecoderReentry
  abiDecoderDynamicLoopSetup abiDecoderTypedContract abiValidMember
  calldataDynOwned calldataDynStep abiDecoderArraySetupInputs
  safeSequence fragExecMem venomMemDefs abiDecoderContract compileEnv emitHelperProps exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Theorem calldata_static_valid_array_setup_sequence:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?prepared. run_inst_seq (emitted_insts st ready) initial = OK prepared /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD (Lit 0w) (Lit 0w)
      0 sb d b cap st.cs_next_var limit_st initial prepared /\ inst_extends st ready
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule_all abi_decoder_coherent_header >> strip_tac >>
  `abi_embedded_static_size ce.ce_struct_fields ty =
   abi_member_head_size (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  `~dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by
    metis_tac[abi_decoder_coherent_dynamic, abi_decoder_needs_offset_iff] >>
  `eval_operand src initial = SOME (n2w sb) /\
   eval_operand dst initial = SOME (n2w d)` by fs[abi_decoder_ranges_def] >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  `abi_decoder_address_frame st.cs_next_var initial prepared` by
    simp[abi_decoder_address_frame_def] >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >>
  disch_then (qspec_then `CALLDATALOAD` assume_tac) >>
  `abi_decoder_operand_live ready.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  suspend "child"
QED

Resume calldata_static_valid_array_setup_sequence[child]:
  qexists_tac `prepared` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [abi_decoder_valid_array_entry_def, LET_THM] >>
  asm_rewrite_tac[] >>
  ho_match_mp_tac (SIMP_RULE bool_ss [LET_THM] abi_decoder_valid_array_child_pre) >>
  asm_simp_tac arith_ss [abi_decode_member_offset_def, GSYM ADD_ASSOC]
QED
Finalise calldata_static_valid_array_setup_sequence

Theorem calldata_static_valid_owned_array_child_entry:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  eval_operand ip initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas iid = SOME (slot,32) /\
  alloca_inv initial /\ slot < dimword (:256) ==>
  frag_exec_mem ctx st ready (\s. s = initial)
    (\t. abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) (Lit 0w) 0 sb d b cap st.cs_next_var limit_st initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial)) (K F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w slot : bytes32) = slot` by simp[] >>
  `mload (w2n (n2w slot : bytes32)) initial = n2w j` by simp[] >>
  `slot+32 <= initial.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all calldata_static_valid_array_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  `eval_operand src initial = SOME (n2w sb) /\
   eval_operand dst initial = SOME (n2w d)` by fs[abi_decoder_ranges_def] >>
  drule_all calldata_element_setup_repeat >> strip_tac >> gvs[] >>
  irule frag_exec_mem_run_inst_seq >> fs[inst_extends_def] >>
  irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
  >- (drule calldata_element_setup_opcodes >> simp[EVERY_MEM]) >>
  ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
  qexistsl_tac [`src`, `n2w slot`] >>
  goal_assum (drule_at Any) >> simp[w2n_n2w] >> metis_tac[]
QED
