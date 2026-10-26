(* Execute dynamic members through the shared actual array-tail pipeline.
   TOP-LEVEL: abi_scratch_dynamic_child_reach preserves complete child input,
   exact head/tail bytes, the parent cursor and one physical enclosing effect. *)
Theory abiScratchDynamicChild
Ancestors
  abiScratchChildSplit abiScratchArrayDynamicTail abiScratchEncoderContract
  abiScratchAddress abiScratchAfterAddress abiScratchFootprint
  abiEncoderAddressReach abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv
  valueEncoding contractABI venomState finite_map words list arithmetic

Theorem abi_scratch_input_address:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_input ei at av prepared src dst sb source_cap d sz first last b cap actual
Proof
  simp_tac bool_ss [abi_scratch_input_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_dynamic_child_reach:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
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
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
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
  drule_all abi_scratch_dynamic_child_split >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `dst`, `rhs` |-> `Lit (n2w ho)`,
    `a` |-> `n2w d:bytes32`, `b` |-> `n2w ho:bytes32`, `st'` |-> `middle`, `out` |-> `head`]
    abi_encoder_binary_reach) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [eval_operand_def] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand head ready = SOME (n2w (d+ho))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`prepared` |-> `middle:compile_state`, `actual` |-> `ready:venom_state`,
    `sz` |-> `output_size:num`]
    abi_scratch_input_address) >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `ready:venom_state`] abi_scratch_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live middle.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr ready = SOME (n2w slot) /\ mload slot ready = n2w off /\
   FLOOKUP ready.vs_allocas site = SOME (slot,32)` by fs[abi_decoder_address_frame_def, mload_def] >>
  mp_tac (Q.INST [`st` |-> `middle:compile_state`, `initial` |-> `ready:venom_state`,
    `data_op` |-> `dst:operand`, `ops` |-> `tail:operand # operand`] abi_scratch_array_dynamic_tail_reach) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (mp_tac (Q.INST [`child_d` |-> `d:num`, `child_lo` |-> `lo:num`,
       `child_hi` |-> `end_st.cs_next_id`, `child_next` |-> `middle.cs_next_var`,
       `child_sz` |-> `output_size:num`, `ready` |-> `ready:venom_state`,
       `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`]
       abi_scratch_effect_after_address) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  drule_all abi_scratch_frame_after_address >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DYNAMIC_CHILD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch dynamic member execution not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDynamicChild");
