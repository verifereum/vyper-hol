(* Actual static and dynamic children extend the canonical tuple prefix.
   TOP-LEVEL: abi_scratch_static_member_step and abi_scratch_dynamic_member_step
   retain physical scratch frames instead of excluding the entire arena. *)
Theory abiScratchMemberStep
Ancestors
  abiScratchMemberAdapter
  abiScratchStatic abiScratchDynamicChild abiScratchPrefix abiScratchEncoderContract
  abiScratchSubset abiScratchFootprint abiEncoderTuple abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding
  valueEncodingProps abiCanonicalWindows contractABI venomState finite_map pred_set words list
  arithmetic

Theorem abi_scratch_input_owned_output:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap s /\
  first <= lo /\ hi <= last ==>
  abi_footprint_disjoint d sz (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)
Proof
  strip_tac >>
  `abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by fs[abi_scratch_input_def] >>
  irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
  simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac
QED

Theorem abi_scratch_static_member_step:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei F heads dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei ty av st src dst sb source_cap d output_size first last b cap initial /\
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+LENGTH (enc ty av) <= hl /\ hl+tails <= output_size /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory /\
    eval_operand out actual = SOME (n2w (LENGTH (enc ty av))) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `heads+LENGTH (enc ty av) <= output_size` by decide_tac >>
  mp_tac (Q.INST [`at` |-> `ty:abi_type`, `offset` |-> `heads:num`] abi_scratch_static_child_spine_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `at` |-> `ty:abi_type`, `sz` |-> `output_size:num`, `s` |-> `initial:venom_state`]
    abi_scratch_input_owned_output) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch
    (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial`] abi_scratch_tuple_static_step) >>
  impl_tac >- gvs[Excl "enc_def"] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_dynamic_member_step:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei T heads dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input ei ty av st src dst sb source_cap d output_size first last b cap initial /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+32 <= hl /\ off = hl+tails /\ off+LENGTH (enc ty av) <= output_size /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory /\
    mload slot actual = n2w (off+LENGTH (enc ty av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc ty av))) /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> `heads+32 <= off` by decide_tac >>
  mp_tac (Q.INST [`at` |-> `ty:abi_type`, `ho` |-> `heads:num`] abi_scratch_dynamic_child_spine_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `lo:num`, `hi` |-> `end_st.cs_next_id`,
    `at` |-> `ty:abi_type`, `sz` |-> `output_size:num`, `s` |-> `initial:venom_state`]
    abi_scratch_input_owned_output) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch
    (abi_decoder_ids lo end_st.cs_next_id) b cap initial`] abi_scratch_tuple_dynamic_step) >>
  impl_tac >- gvs[Excl "enc_def"] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [GSYM mem_word_at_eq_mload]
QED
