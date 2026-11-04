(* The real decoder index allocator/store uses only its physical scratch interval. *)
Theory abiScratchDecoderIndex
Ancestors
  abiScratchOwnedPrefix abiScratchPrefix abiScratchEncoderContract abiScratchDecoderContract
  abiEncoderArrayParent abiEncoderComplexPrefix abiEncoderMembersDefs abiDecoderIndexInit
  abiDecoderAllocation abiDecoderFootprint abiDecoderReentry abiDecoderLoop abiDecoderFrame
  compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_decoder_index:
  abi_decode_index_init st = (index_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. eval_operand index_ptr actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
    abi_decoder_operand_live st'.cs_next_var index_ptr /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d sz b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (index_ptr,st')` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < st'.cs_next_id` by decide_tac >>
  drule_all abi_scratch_owned_prefix_reach >>
    disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  rename1 `abi_encoder_cursor T index_ptr st.cs_next_id slot first st.cs_next_id st' _ actual` >>
  mp_tac (Q.INST [`infos` |-> `[]:(abi_enc_info # num # num # bool) list`,
    `dyn_ptr` |-> `index_ptr:operand`, `next` |-> `st.cs_next_var`,
    `site` |-> `st.cs_next_id`, `stop` |-> `st'.cs_next_id`]
    abi_scratch_prefix_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`actual`, `slot`] >> fs[abi_encoder_cursor_def]
QED
