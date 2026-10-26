(* Computed tail initialization preserves complete array input and output data.
   TOP-LEVEL: abi_scratch_array_tail_input adds the actual tail cursor to the
   precise execution result, retaining every previously initialized cursor. *)
Theory abiScratchArrayTailInput
Ancestors
  abiScratchArrayTail abiScratchFootprint abiEncoderArrayTailInitCode
  abiEncoderComplexPrefixReach abiEncoderArrayFrame abiEncoderArrayPrefix
  abiEncoderMembersDefs abiEncoderInput abiEncoderInputFrame
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  abiDecoderLoop compileEnv valueEncoding contractABI venomState
  finite_map pred_set words list arithmetic

Theorem abi_scratch_array_tail_input:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual tail_slot.
    abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs j d actual.vs_memory /\
    abi_encoder_cursor T dyn_ptr st.cs_next_id tail_slot first st.cs_next_id st'
      (LENGTH avs*asz) actual /\
    (!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
      abi_encoder_cursor T op site slot first lo st' off actual) /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,LENGTH avs*asz,0,F)] dyn_ptr
      st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_tail_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `has_type (Array NONE ty) (ListV avs)` by
    (drule abi_encoder_input_typed >> simp[]) >>
  `abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap actual.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  `abi_encoder_array_prefix ty avs j d actual.vs_memory` by
    (drule_all abi_encoder_array_prefix_output_frame >> simp[]) >>
  `abi_decoder_operand_live st'.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`,
       `cap` |-> `cap:num`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `sb:num`, `n` |-> `source_cap:num`] abi_scratch_disjoint_advance) >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`,
       `cap` |-> `cap:num`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
       `p` |-> `d:num`, `n` |-> `output_size:num`] abi_scratch_disjoint_advance) >> simp[]) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[abi_encoder_cursor_def] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_TAIL_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array tail input not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayTailInput");
