(* The real static-array exit reloads the count and returns the exact ABI length.
   TOP-LEVEL: abi_scratch_array_static_scalar_exit preserves complete output
   and composes its address-only effect from the loop origin. *)
Theory abiScratchArrayStaticExit
Ancestors
  abiScratchArrayLoopInvariant abiScratchArrayLoopExit abiScratchArrayCount abiScratchAddress
  abiScratchEffect abiScratchEncoderContract abiEncoderArrayExit abiEncoderArrayLayout
  abiEncoderMembersDefs abiDecoderDynamicLoopSetup abiDecoderLoop abiDecoderReentry
  abiDecoderContract compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_array_static_scalar_exit:
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial /\
  abi_encode_array_static_exit src asz st = (out,final) /\ fn_has_code st final func /\
  owner_st.cs_next_var <= st.cs_next_var /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  label = st.cs_current_bb /\ st.cs_current_insts = [] ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_array_loop_output >> strip_tac >>
  drule abi_scratch_array_loop_inv_facts >> strip_tac >>
  qpat_assum `abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op label (LENGTH avs) origin initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `~is_dynamic ty` by fs[] >> drule_all abi_encoder_array_static_size >> disch_tac >>
  mp_tac (Q.INST [`cnt` |-> `LENGTH (avs:abi_value list)`] abi_encode_array_static_exit_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `site:num`, `next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`]
    abi_scratch_address_effect) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `site`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> fs[abi_decoder_address_frame_def]
QED
