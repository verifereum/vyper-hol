(* Actual array body coordinates establish the precise recursive child input.
   TOP-LEVEL: abi_scratch_array_prepare executes the generated address prefix
   and derives child separation from full parent buffers and scratch evolution. *)
Theory abiScratchArrayPrepare
Ancestors
  abiScratchInput abiScratchEncoderContract abiScratchAddress abiScratchFootprint
  abiEncoderArrayAddress abiEncoderArrayLayout abiEncoderArrayBounds abiEncoderInput
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderLoop abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_array_child_capacity:
  has_type (Array NONE ty) (ListV avs) /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size ==>
  32 <= output_size /\ LENGTH (enc ty (EL j avs)) <= output_size-32
Proof
  strip_tac >> drule_all abi_encoder_array_child_bounds >> strip_tac >>
  Cases_on `is_dynamic ty` >> fs[] >> decide_tac
QED

Theorem abi_scratch_array_prepare:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
  fn_has_code st prepared func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    abi_scratch_input ei ty (EL j avs) prepared (SND (FST coords)) (FST (SND coords))
      (sb+32+j*msz) msz (d+32) (output_size-32) first last b cap actual /\
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    asz = abi_member_head_size ty /\ active = is_dynamic ty /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  drule_all abi_encode_array_addresses_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  `has_type (Array NONE ty) (ListV avs)` by
    (qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
       (ACCEPT_TAC o MATCH_MP abi_encoder_input_typed)) >>
  drule_all abi_scratch_array_child_capacity >> strip_tac >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
    `next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
    abi_scratch_address) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `sb <= sb+32+j*msz /\ sb+32+j*msz+msz <= sb+source_cap /\
   d <= d+32 /\ d+32+(output_size-32) <= d+output_size` by decide_tac >>
  `abi_encoder_input ei ty (EL j avs) (sb+32+j*msz) msz actual.vs_memory` by gvs[] >>
  mp_tac (Q.INST [`parent_ei` |-> `AbiDynArray ei asz msz active`,
    `parent_at` |-> `Array NONE ty`, `parent_av` |-> `ListV avs`, `parent_src` |-> `src`,
    `parent_dst` |-> `dst`, `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `dst` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`, `at` |-> `ty:abi_type`,
    `av` |-> `EL j (avs:abi_value list)`, `child_sb` |-> `sb+32+j*msz`, `child_cap` |-> `msz:num`,
    `child_d` |-> `d+32`, `child_size` |-> `output_size-32`] abi_scratch_input_regions) >>
  impl_tac >- gvs[] >> disch_tac >>
  qexists_tac `actual` >> gvs[]
QED
