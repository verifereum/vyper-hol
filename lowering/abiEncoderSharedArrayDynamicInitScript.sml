(* Dynamic initializer assembly: shared index and tail allocation boundaries. *)
Theory abiEncoderSharedArrayDynamicInit
Ancestors
  abiEncoderSharedArrayIndexInit abiEncoderSharedArrayTailInit abiEncoderArrayDynamicInit
  abiEncoderSharedArrayInput abiEncoderSharedContract abiEncoderRegisteredEffect abiEncoderExtendSim
  abiEncoderArrayCursor abiEncoderMembersDefs abiEncoderArrayPrefix abiScratchCursor
  abiScratchEffect abiScratchEncoderContract abiDecoderAllocation abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState words list arithmetic pred_set

Theorem abi_encoder_shared_array_dynamic_init:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
  fn_has_code start owner_st func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual index_slot tail_slot.
    abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
      (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id owner_st 0 actual /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
      (LENGTH avs*abi_member_head_size ty) actual /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = owner_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ owner_st.cs_next_id <= last /\
   start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_x_assum `T <=> is_dynamic ty` (assume_tac o REWRITE_RULE [EQ_CLAUSES]) >>
  drule_all abi_encoder_shared_array_index_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `indexed` (qx_choose_then `index_slot` strip_assume_tac))) >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `fresh_vars_wrt limit_st indexed /\ abi_decoder_budget first last b cap indexed` by
    fs[abi_scratch_effect_def] >>
  drule_all abi_encoder_shared_array_tail_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` (qx_choose_then `tail_slot` strip_assume_tac))) >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 actual` by
    (qpat_assum `abi_encoder_shared_input _ (after_index,_,_) _ _ _ indexed`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
     irule abi_scratch_cursor_protected >>
     goal_assum (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 actual` by
    (irule abi_encoder_cursor_mono >> qexists_tac `after_index` >> simp[]) >>
  `abi_encoder_cursor T dyn_ptr (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
    (LENGTH avs*abi_member_head_size ty) actual` by
    (gvs[abi_encoder_cursor_def, Excl "enc_def"] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial indexed` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap indexed actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `indexed` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial indexed` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] indexed actual` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `indexed` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `indexed` >> asm_rewrite_tac []) >>
  qexistsl_tac [`actual`,`index_slot`,`tail_slot`] >> gvs[Excl "enc_def"]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared dynamic init admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_dynamic_init];
