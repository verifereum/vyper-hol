(* Execute the actual static child helper under the precise encoder contract.
   TOP-LEVEL: abi_scratch_static_info_reach returns the exact child window and
   an enclosing physical effect. Helpers select a bounded destination and
   derive the contract for word/copy/empty static leaves. *)
Theory abiScratchStaticInfo
Ancestors
  abiScratchEncoderLeaves abiScratchEncoderRun abiScratchChildInput abiScratchEncoderContract
  abiScratchFootprint abiScratchEffectWiden abiEncoderAdmissible abiEncoderLeafCode
  abiDecoderAllocation abiDecoderFootprint abiDecoderCorrectWord abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderFrame abiDecoderLoop abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_static_leaf:
  abi_encoder_static_leaf ei ==> abi_scratch_encoder ei
Proof
  rw[abi_encoder_static_leaf_def] >>
  simp[abi_scratch_encoder_word, abi_scratch_encoder_copy, abi_scratch_encoder_empty]
QED

Theorem abi_scratch_input_offset:
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size ==>
  abi_scratch_input ei at av st src head sb source_cap (d+offset) (LENGTH (enc at av))
    first last b cap initial
Proof
  strip_tac >>
  `abi_decoder_address_frame st.cs_next_var initial initial` by simp[abi_decoder_address_frame_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial initial` by
    (irule abi_scratch_evolution_refl >> drule abi_decoder_budget_frontier >> simp[]) >>
  mp_tac (Q.INST [`prepared` |-> `st:compile_state`, `actual` |-> `initial:venom_state`,
    `child_dst` |-> `head:operand`, `off` |-> `offset:num`] abi_scratch_child_input_address) >>
  asm_simp_tac bool_ss [LESS_EQ_REFL]
QED

Theorem abi_scratch_static_info_reach:
  abi_encoder_static_leaf ei /\ compile_abi_encode_static_info head src ei st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand head initial = SOME (n2w (d+offset)) /\ offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame
      ((d+offset,LENGTH (enc at av))::abi_decoder_child_scratch
        (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_static_leaf >> disch_tac >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_scratch_input_offset >> disch_tac >>
  mp_tac (Q.INST [`start` |-> `st`, `dst` |-> `head:operand`, `d` |-> `d+offset`]
    abi_scratch_encoder_run) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_STATIC_INFO_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch actual static helper not kernel closed: " ^ n)
  end) (DB.thms "abiScratchStaticInfo");
