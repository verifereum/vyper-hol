(* Preserve a method prefix through recursive encoding and the final length store.
   TOP-LEVEL: abi_scratch_builtin_compose returns one physical enclosing effect.
   Its prefix observation follows from physical windows and owned scratch IDs. *)
Theory abiScratchBuiltinCompose
Ancestors
  abiScratchBuiltinFinish abiScratchEncoderContract abiScratchEffect abiScratchSubset
  abiScratchFootprint abiEncoderArrayFrame abiBuiltinEncodeCode abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop
  compileEnv venomState pred_set words list arithmetic

Theorem abi_scratch_builtin_prefix_frame:
  abi_scratch_effect first last lo hi next limit_st (p+32+mid_size) len b cap s t /\
  first <= lo /\ hi <= last /\
  abi_footprint_disjoint p (32+mid_size+len)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) ==>
  mem_bytes_at (p+32) mid_size t.vs_memory = mem_bytes_at (p+32) mid_size s.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint (p+32) mid_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`p`, `32+mid_size+len`] >> simp[]) >>
  `abi_footprint_disjoint (p+32) mid_size
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
     simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  irule abi_decode_footprint_frame_slice >>
  qexists_tac `((p+32+mid_size,len)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` >>
  simp[abi_scratch_disjoint_cons] >> fs[abi_scratch_effect_def]
QED

Theorem abi_scratch_builtin_compose:
  abi_scratch_effect first last ready.cs_next_id body_end.cs_next_id ready.cs_next_var
    limit_st (p+32+mid_size) len b cap initial encoded /\
  mem_bytes_at (p+32+mid_size) len encoded.vs_memory = bytes /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_builtin_encode_finish buf encoded_len mid_size body_end = ((),final) /\
  fn_has_code body_end final func /\ ready.cs_next_var <= body_end.cs_next_var /\
  body_end.cs_next_id <= final.cs_next_id /\
  p < dimword (:256) /\ first <= ready.cs_next_id /\ final.cs_next_id <= last /\
  abi_footprint_disjoint p (32+mid_size+len)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  ~encoded.vs_halted /\ encoded.vs_current_bb = body_end.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH body_end.cs_current_insts /\ abi_decode_sim ctx func initial encoded ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32+mid_size) len actual.vs_memory = bytes /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+len) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `body_end.cs_next_id <= last` by decide_tac >>
  drule_all abi_scratch_builtin_prefix_frame >> disch_tac >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live body_end.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> simp[]) >>
  `fresh_vars_wrt limit_st encoded /\ abi_decoder_budget first last b cap encoded` by
    fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`st` |-> `body_end`, `initial` |-> `encoded:venom_state`,
    `output_size` |-> `32+mid_size+len:num`, `lo` |-> `ready.cs_next_id`,
    `hi` |-> `final.cs_next_id`] abi_scratch_builtin_finish) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (32+mid_size+len) b cap initial encoded` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p+32+mid_size`, `body_end.cs_next_id`,
       `ready.cs_next_id`, `ready.cs_next_var`, `len`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (32+mid_size+len) b cap encoded actual` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p`, `final.cs_next_id`,
       `ready.cs_next_id`, `body_end.cs_next_var`, `32+mid_size+len`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (32+mid_size+len) b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `encoded` >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED
