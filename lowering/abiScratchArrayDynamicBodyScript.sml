(* Complete actual dynamic-element body with physical scratch separation.
   TOP-LEVEL: abi_scratch_array_dynamic_body_reach composes the seven address
   instructions with recursive child execution and cursor bookkeeping.
   Helper: exact head/tail bounds are derived from complete typed array input. *)
Theory abiScratchArrayDynamicBody
Ancestors
  abiScratchArrayPrepare abiScratchArrayDynamicTail abiScratchAfterAddress
  abiScratchEncoderContract abiScratchEffectProtected abiScratchFootprint
  abiEncoderArrayDynamicCode abiEncoderArrayAddress abiEncoderArrayBounds abiEncoderArrayLayout
  abiEncoderInput abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv
  valueEncoding contractABI venomState finite_map words list arithmetic

Theorem abi_scratch_array_body_bounds:
  abi_encoder_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs) sb source_cap mem /\
  j < LENGTH avs /\ LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) ==>
  has_type (Array NONE ty) (ListV avs) /\ is_dynamic ty /\ asz = abi_member_head_size ty /\
  32 <= output_size /\ j*asz+32 <= off /\ off+LENGTH (enc ty (EL j avs)) <= output_size-32
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
    (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  `is_dynamic ty` by fs[] >> drule_all abi_encoder_array_child_bounds >> strip_tac >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem abi_scratch_array_dynamic_body_reach:
  abi_scratch_encoder ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame
      ([(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)))] ++
        abi_decoder_child_scratch (abi_decoder_ids site end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last site end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `addressed.cs_next_var <= limit_st.cs_next_var /\ site < addressed.cs_next_id /\
   st.cs_next_var <= addressed.cs_next_var` by decide_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_scratch_array_body_bounds >> strip_tac >>
  mp_tac (Q.INST [`prepared` |-> `addressed`, `active` |-> `T`] abi_scratch_array_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `abi_decoder_operand_live addressed.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr ready = SOME (n2w slot) /\ mload slot ready = n2w off /\
   FLOOKUP ready.vs_allocas site = SOME (slot,32)` by
    fs[abi_decoder_address_frame_def, mload_def] >>
  mp_tac (Q.INST [`st` |-> `addressed`, `initial` |-> `ready:venom_state`,
    `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `data_op` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`,
    `head` |-> `SND (SND (coords:(operand # operand) # (operand # operand)))`,
    `at` |-> `ty:abi_type`, `av` |-> `EL j (avs:abi_value list)`, `ho` |-> `j*asz`,
    `sb` |-> `sb+32+j*msz`, `source_cap` |-> `msz:num`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`, `lo` |-> `site:num`] abi_scratch_array_dynamic_tail_reach) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (mp_tac (Q.INST [`op` |-> `FST (FST (coords:(operand # operand) # (operand # operand)))`,
       `w` |-> `n2w j:bytes32`, `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`,
       `next` |-> `addressed.cs_next_var`, `d` |-> `d+32`, `sz` |-> `output_size-32`,
       `lo` |-> `site:num`, `hi` |-> `end_st.cs_next_id`] abi_scratch_effect_operand) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids site end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
    `fp` |-> `[(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)))]`]
    abi_scratch_frame_after_address) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_lo` |-> `site:num`, `child_hi` |-> `end_st.cs_next_id`,
    `child_next` |-> `addressed.cs_next_var`, `child_d` |-> `d+32`, `child_sz` |-> `output_size-32`,
    `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`, `lo` |-> `site:num`,
    `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  qexists_tac `actual` >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_DYNAMIC_BODY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch complete dynamic body not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayDynamicBody");
