(* Execute setup, the recursive child and bookkeeping in the containing CFG.
   TOP-LEVEL: abi_scratch_array_dynamic_tail_reach composes all three actual
   stages under the child induction hypothesis and returns one precise effect. *)
Theory abiScratchArrayDynamicTail
Ancestors
  abiScratchArrayTail abiScratchEncoderRun abiScratchChild abiScratchEncoderContract
  abiScratchFootprint abiScratchEffect abiEncoderArrayTail abiEncoderChildCode
  abiEncoderChildSuffixReach abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding
  contractABI venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_array_dynamic_tail_reach:
  abi_scratch_encoder ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\ eval_operand head initial = SOME (n2w (d+ho)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_word_at (d+ho) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand child_len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    abi_decode_footprint_frame
      ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
        abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_array_tail_code >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_scratch_array_tail_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `FLOOKUP ready.vs_allocas site = SOME (slot,32) /\
   eval_operand head ready = SOME (n2w (d+ho))` by fs[abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`start` |-> `prepared`, `end_st` |-> `child_end`, `initial` |-> `ready:venom_state`,
    `dst` |-> `SND (ops:operand # operand)`, `out` |-> `child_len`, `d` |-> `d+off`,
    `offset` |-> `FST (ops:operand # operand)`, `h` |-> `d+ho`] abi_scratch_dynamic_child_core) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap ready encoded` by
    fs[abi_scratch_effect_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial encoded` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`, `cap` |-> `cap:num`,
       `p` |-> `d:num`, `n` |-> `output_size:num`, `s` |-> `initial:venom_state`,
       `t` |-> `encoded:venom_state`] abi_scratch_disjoint_advance) >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `out` |-> `child_len`,
    `initial` |-> `encoded:venom_state`, `offset` |-> `FST (ops:operand # operand)`,
    `h` |-> `d+ho`, `len` |-> `LENGTH (enc at av)`, `bytes` |-> `enc at av`]
    abi_scratch_child_finish) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `child_end.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `suffix_st` |-> `child_end`, `q` |-> `d+off`,
    `len` |-> `LENGTH (enc at av)`, `sz` |-> `output_size:num`, `next` |-> `st.cs_next_var`,
    `hi` |-> `end_st.cs_next_id`, `h` |-> `d+ho`, `out` |-> `child_len`] abi_scratch_child_effect) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `abi_encoder_input ei at av sb source_cap actual.vs_memory` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `st` |-> `st:compile_state`, `dst` |-> `data_op:operand`, `d` |-> `d:num`,
       `sz` |-> `output_size:num`, `lo` |-> `lo:num`, `hi` |-> `end_st.cs_next_id`,
       `next` |-> `st.cs_next_var`] abi_scratch_effect_source) >>
     impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED
