(* Physical interpretation of the common array execution spine. *)
Theory abiScratchArraySpine
Ancestors
  abiEncoderArraySourceSpine abiScratchMemberAdapter abiEncoderMemberPhaseRaw
  abiEncoderMemberSpine abiEncoderArrayTail abiScratchAddress abiScratchChild
  abiScratchEncoderContract abiScratchEffect abiScratchFootprint
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFrame abiDecoderReentry
  abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI venomState
  words list arithmetic

Theorem abi_scratch_array_prepare_raw_transport:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
    (LENGTH (enc at av)) first last b cap ready /\
  eval_operand (FST ops) ready = SOME (n2w off) /\
  eval_operand dyn_ptr ready = SOME (n2w slot) /\
  abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
  abi_decoder_operand_live prepared.cs_next_var (SND ops) /\
  abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready /\
  abi_decoder_address_frame st.cs_next_var initial ready /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial ready /\
  ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
  ~ready.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand data_op initial = SOME (n2w d) /\ abi_decoder_operand_live st.cs_next_var data_op` by
    fs[abi_scratch_input_def] >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  drule_all abi_encoder_member_tail_transport >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `ready:venom_state`, `ids` |-> `abi_decoder_ids first last`] abi_scratch_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
    (LENGTH (enc at av)) first last b cap ready` by
    (drule_at (Pat `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       abi_scratch_child_input_address >>
     disch_then (drule_at_then (Pat `abi_decoder_address_frame _ _ _`) mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_encoder_array_tail_raw_control >> strip_tac >>
  fs[abi_decoder_address_frame_def]
QED
