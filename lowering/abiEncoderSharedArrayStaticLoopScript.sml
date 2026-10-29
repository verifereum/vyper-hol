(* Static loop assembly through shared initialization and prepared execution. *)
Theory abiEncoderSharedArrayStaticLoop
Ancestors
  abiEncoderSharedArrayRun abiEncoderSharedArrayIndexInit abiEncoderArrayLoopCode
  abiEncoderSharedContract abiEncoderRegisteredEffect abiEncoderExtendSim
  abiEncoderArrayPrefix abiEncoderMembersDefs abiScratchEffect abiScratchEncoderContract
  abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI venomState
  words list arithmetic pred_set

Theorem abi_encoder_shared_array_static_loop:
  abi_encoder_shared ei /\ abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_id <= hi /\
   owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (fs[abi_encoder_array_loop_code_def] >> decide_tac) >>
  drule_all abi_encoder_shared_array_index_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot` strip_assume_tac))) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  `mem_word_at d ready.vs_memory = n2w (LENGTH avs)` by
    fs[abi_encoder_array_prefix_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `ready:venom_state`,
    `site` |-> `start.cs_next_id`] abi_encoder_shared_array_prepared_complete) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial ready` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap ready actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial ready` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
