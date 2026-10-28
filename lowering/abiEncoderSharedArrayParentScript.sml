(* Parent allocation/count composition with open source windows. *)
Theory abiEncoderSharedArrayParent
Ancestors
  abiEncoderSharedArrayPrepare abiEncoderSharedArrayCountPrepare abiEncoderSharedArrayInput
  abiEncoderSharedContract abiEncoderArrayParent abiEncoderArrayPrefix abiEncoderArrayCursor
  abiEncoderMembersDefs abiEncoderComplexPrefix abiScratchCursor abiScratchEffect
  abiScratchEncoderContract abiEncoderRegisteredEffect abiEncoderExtendSim
  abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv
  valueEncoding contractABI venomState words list arithmetic pred_set

Theorem abi_encoder_shared_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
      (loop_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id loop_st.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_encode_array_prefix_context >>
  disch_then (qx_choose_then `parent_ptr` (qx_choose_then `allocated` (qx_choose_then `cnt` strip_assume_tac))) >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= last /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  drule_all abi_encoder_shared_cursor_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `middle` (qx_choose_then `slot` strip_assume_tac))) >>
  `abi_decoder_budget first last b cap middle /\ fresh_vars_wrt limit_st middle` by fs[abi_scratch_effect_def] >>
  drule_all abi_encoder_shared_array_count_prepare >>
  disch_then (qspecl_then [`allocated.cs_next_id`,`loop_st.cs_next_id`,`ctx`]
    (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 middle` by fs[] >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 actual` by
    (qpat_assum `abi_encoder_shared_input _ (allocated,_,_) _ _ _ middle`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
     drule abi_scratch_cursor_protected >> disch_then drule >> simp[] >>
     disch_then irule >> simp[] >> decide_tac) >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id loop_st 0 actual` by
    (irule abi_encoder_cursor_mono >> qexists_tac `allocated` >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial middle` by
    (qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial middle`
       (mp_then Any mp_tac abi_scratch_effect_widen) >>
     disch_then irule >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d sz b cap middle actual` by
    (qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ middle actual`
       (mp_then Any mp_tac abi_scratch_effect_widen) >>
     disch_then irule >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_rewrite_tac [] >> qexists_tac `middle` >> gvs[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id loop_st.cs_next_id) [(d,sz)] initial middle` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >> simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id loop_st.cs_next_id) [(d,sz)] middle actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >> simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id loop_st.cs_next_id) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `middle` >> simp[]) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `middle` >> simp[]) >>
  qexistsl_tac [`actual`,`slot`] >> gvs[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared parent preparation admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_parent_prepare];
