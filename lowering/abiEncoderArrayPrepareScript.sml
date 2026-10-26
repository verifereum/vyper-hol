(* Complete parent source data establishes the selected child's real buffer input. *)
Theory abiEncoderArrayPrepare
Ancestors
  abiEncoderArrayLayout abiEncoderArrayAddressReach abiEncoderArrayAddress abiEncoderArrayCode
  abiEncoderChildInputs abiEncoderInput abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_encoder_array_child_buffer:
  abi_encoder_buffer_pre (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  j < LENGTH avs /\ LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  abi_decoder_operand_live prepared.cs_next_var child_src /\
  abi_decoder_operand_live prepared.cs_next_var data_op /\
  eval_operand child_src actual = SOME (n2w (sb+32+j*msz)) /\
  eval_operand data_op actual = SOME (n2w (d+32)) ==>
  abi_encoder_buffer_pre ei ty (EL j avs) prepared child_src data_op
    (sb+32+j*msz) msz (d+32) (output_size-32) b cap actual /\
  asz = abi_member_head_size ty /\ dyn = is_dynamic ty
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
    (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  drule abi_encoder_array_encoding_bound >> strip_tac >>
  `32 <= output_size /\ d+32+(output_size-32) = d+output_size` by decide_tac >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  asm_simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_array_prepare:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
  fn_has_code st prepared func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready. abi_encoder_buffer_pre ei ty (EL j avs) prepared
      (SND (FST coords)) (FST (SND coords)) (sb+32+j*msz) msz (d+32) (output_size-32) b cap ready /\
    asz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
    eval_operand (FST (FST coords)) ready = SOME (n2w j) /\
    eval_operand (SND (SND coords)) ready = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `prepared`] abi_encode_array_addresses_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`,
    `child_src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `data_op` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`]
    abi_encoder_array_child_buffer) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder selected array input not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayPrepare");
