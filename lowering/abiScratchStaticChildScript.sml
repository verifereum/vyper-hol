(* Execute a member's static placement under its recursive child hypothesis.
   TOP-LEVEL: abi_scratch_static_child_reach follows the actual head ADD and
   child encoder, retaining its narrow physical write frame. *)
Theory abiScratchStaticChild
Ancestors
  abiScratchEncoderRun abiScratchChildInput abiScratchAfterAddress abiScratchAddress
  abiScratchFrameCompose abiScratchEncoderContract abiScratchFootprint
  abiEncoderStaticChild abiEncoderAddressReach abiEncoderChildFrames
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState pred_set words list arithmetic

Theorem abi_scratch_child_frame_after_address:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo hi child_next limit_st d sz b cap ready actual /\
  lo <= child_lo ==>
  abi_decode_footprint_frame
    ([(d,sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual
Proof
  strip_tac >>
  `abi_decoder_ids child_lo hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_decode_footprint_frame
    ([(d,sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap ready) ready actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`,
       `child_ids` |-> `abi_decoder_ids child_lo hi`, `fp` |-> `[(d,sz)]`,
       `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_frame_subset_append) >>
     impl_tac >- (asm_simp_tac (srw_ss()) [] >> fs[abi_scratch_effect_def]) >> simp[]) >>
  drule_all abi_scratch_frame_after_address >> simp[]
QED

Theorem abi_scratch_static_child_reach:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame
      ([(d+offset,LENGTH (enc at av))] ++ abi_decoder_child_scratch
        (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_context >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `dst`, `rhs` |-> `Lit (n2w offset)`,
    `a` |-> `n2w d:bytes32`, `b` |-> `n2w offset:bytes32`, `st'` |-> `prepared`, `out` |-> `head`]
    abi_encoder_binary_reach) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [eval_operand_def] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand head ready = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `ready:venom_state`, `ids` |-> `abi_decoder_ids first last`] abi_scratch_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_input ei at av prepared src head sb source_cap (d+offset)
    (LENGTH (enc at av)) first last b cap ready` by
    (mp_tac (Q.INST [`prepared` |-> `prepared:compile_state`, `actual` |-> `ready:venom_state`,
       `child_dst` |-> `head:operand`, `off` |-> `offset:num`] abi_scratch_child_input_address) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`start` |-> `prepared`, `initial` |-> `ready:venom_state`,
    `dst` |-> `head:operand`, `d` |-> `d+offset`] abi_scratch_encoder_run) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (mp_tac (Q.INST [`child_d` |-> `d+offset`, `child_lo` |-> `prepared.cs_next_id`,
       `child_hi` |-> `end_st.cs_next_id`, `child_next` |-> `prepared.cs_next_var`,
       `child_sz` |-> `LENGTH (enc at av)`, `ready` |-> `ready:venom_state`,
       `lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `child_lo` |-> `prepared.cs_next_id`,
    `hi` |-> `end_st.cs_next_id`, `child_next` |-> `prepared.cs_next_var`, `next` |-> `st.cs_next_var`,
    `d` |-> `d+offset`, `sz` |-> `LENGTH (enc at av)`] abi_scratch_child_frame_after_address) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_STATIC_CHILD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch static member execution not kernel closed: " ^ n)
  end) (DB.thms "abiScratchStaticChild");
