(* Complete array construction by composing established rich phase boundaries. *)
Theory abiEncoderSharedArrayOuter
Ancestors
  abiEncoderSharedArrayParent abiEncoderSharedArraySelectedLoop abiEncoderSharedArrayFinishProtected
  abiEncoderSharedContract abiScratchPhaseCompose abiEncoderArrayContext abiEncoderMembersDefs
  abiEncoderRegisteredEffect abiEncoderExtendSim abiScratchEffect abiScratchEncoderContract
  abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic pred_set

Theorem abi_encoder_shared_array_outer:
  abi_encoder_shared ei /\ (~active ==> abi_encoder_static_leaf ei) /\
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_context >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_end.cs_next_id <= last /\
   loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_end.cs_next_var <= limit_st.cs_next_var /\
   start.cs_next_id < loop_st.cs_next_id /\ start.cs_next_id < final.cs_next_id /\
   first <= loop_st.cs_next_id /\ start.cs_next_var <= loop_st.cs_next_var /\
   loop_end.cs_next_id <= final.cs_next_id` by decide_tac >>
  drule_all abi_encoder_shared_array_parent_prepare >>
  disch_then (qspec_then `ctx` (qx_choose_then `ready` (qx_choose_then `slot` strip_assume_tac))) >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by fs[abi_scratch_effect_def] >>
  drule_all (Q.INST [`hi` |-> `final.cs_next_id`] abi_encoder_shared_array_selected_loop
    |> REWRITE_RULE [LESS_EQ_REFL, AND_CLAUSES]) >>
  disch_then (qspec_then `ctx` (qx_choose_then `encoded` strip_assume_tac)) >>
  qpat_assum `abi_encoder_shared_input _ (loop_st,_,_) _ _ _ ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule_all abi_encoder_shared_array_finish_protected >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `start.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  drule_all abi_scratch_phase_compose >> disch_tac >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial ready` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] ready encoded` by
    (irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF, abi_decoder_ids_def]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial encoded` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id final.cs_next_id) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial encoded` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `ready` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `encoded` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
