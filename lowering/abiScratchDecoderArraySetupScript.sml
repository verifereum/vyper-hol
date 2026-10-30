(* Actual array-address instructions, for both static and dynamic child layouts. *)
Theory abiScratchDecoderArraySetup
Ancestors
  abiScratchDecoderContract abiScratchDecoderRanges abiScratchDecoderTuple
  abiDecoderValidArraySetupInputs abiDecoderValidArraySetupInputs abiDecoderArraySetupInputs
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup abiDecoderDynamic abiDecoderOffset
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderLoop abiDecodeRanges abiValidMember abiValidMembers abiEncoder fragExec instIdxIndep
  compileEnv valueEncoding vyperABI vyperValue contractABI venomState venomExecSemantics words
  list arithmetic

Definition abi_scratch_decoder_array_setup_post_def:
  abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d next limit_st initial t <=>
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + (32 +
      abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
        (j * abi_member_head_size (vyper_to_abi_type env ty))))) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame next initial t
End

Theorem abi_scratch_decoder_array_setup_post_inst_idx[simp]:
  abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d next limit_st initial
    (t with vs_inst_idx := ix) <=>
  abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d next limit_st initial t
Proof
  simp[abi_scratch_decoder_array_setup_post_def, abi_decoder_address_frame_def,
    fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_scratch_decoder_array_static_prefix:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf ty tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?t. run_inst_seq (emitted_insts st ready) initial = OK t /\
    abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d
      st.cs_next_var limit_st initial t /\ inst_extends st ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qpat_assum `abi_decoder_header ce env ty tv`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_header_def]) >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  `~abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by fs[is_dynamic_def] >>
  `~dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by
    metis_tac[abi_decoder_static_needs_no_offset] >>
  `~is_abi_dynamic ce.ce_struct_fields ty` by fs[is_dynamic_def] >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK t` >>
  qexists_tac `t` >>
  asm_simp_tac bool_ss [abi_scratch_decoder_array_setup_post_def,
    abi_decode_member_offset_def, is_dynamic_def, abi_decoder_address_frame_def, GSYM ADD_ASSOC]
QED

Theorem abi_scratch_decoder_array_dynamic_prefix:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < abi_head_word bs /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?t. run_inst_seq (emitted_insts st ready) initial = OK t /\
    abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d
      st.cs_next_var limit_st initial t /\ inst_extends st ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_ranges_point >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_decoder_valid_array_setup_inputs) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK t` >>
  qexists_tac `t` >> asm_simp_tac bool_ss [abi_scratch_decoder_array_setup_post_def, GSYM ADD_ASSOC]
QED

Theorem abi_scratch_decoder_array_setup_sequence:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?t. run_inst_seq (emitted_insts st ready) initial = OK t /\
    abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d
      st.cs_next_var limit_st initial t /\ inst_extends st ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `j < abi_head_word bs` by asm_simp_tac bool_ss [] >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  fs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  FIRST [drule_all abi_scratch_decoder_array_dynamic_prefix >> simp[],
    drule_all abi_scratch_decoder_array_static_prefix >> simp[]]
QED
