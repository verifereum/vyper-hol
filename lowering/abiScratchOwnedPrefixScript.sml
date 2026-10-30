(* Actual cursor initialization with a frame confined to its compiler interval.
   TOP-LEVEL: abi_scratch_owned_prefix_reach executes the generated initializer;
   abi_scratch_owned_prefix_parent preserves an already-live ancestor cursor. *)
Theory abiScratchOwnedPrefix
Ancestors
  abiScratchPrefixReach abiScratchFootprint abiEncoderComplexPrefix abiEncoderMembersDefs
  abiEncoderArrayHeaderMemory abiDecoderFootprint abiDecoderAllocation abiDecoderFrame
  abiDecoderContract abiDecoderReentry abiDecoderLoop compileEnv venomState finite_map pred_set
  words list arithmetic

Theorem abi_scratch_owned_prefix_frame:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  first <= site /\ site < stop /\ stop <= last ==>
  abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids site stop) b cap initial) initial actual
Proof
  strip_tac >>
  `abi_decoder_ids site stop SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_scratch_evolution (abi_decoder_ids site stop) b cap initial actual` by
    (drule_all abi_scratch_evolution_subset >> simp[]) >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids site stop`, `site` |-> `site:num`,
    `slot` |-> `slot:num`, `sz` |-> `32`, `s` |-> `initial:venom_state`,
    `t` |-> `actual:venom_state`] abi_scratch_final_slot_frame) >>
  simp[abi_decoder_ids_def]
QED

Theorem abi_scratch_owned_prefix_reach:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`]
    abi_scratch_encoder_prefix_reach) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `st.cs_next_id < st'.cs_next_id` by decide_tac >>
  drule_all abi_scratch_owned_prefix_frame >> disch_then assume_tac >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_owned_prefix_parent:
  abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
    limit_st first last b cap initial actual /\
  abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
    initial actual /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st.cs_next_id <= st'.cs_next_id /\ st.cs_next_var <= st'.cs_next_var /\
  abi_encoder_cursor T parent_ptr parent_site parent_slot first lo st off initial ==>
  abi_encoder_cursor T parent_ptr parent_site parent_slot first lo st' off actual
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_cursor_def]) >>
  `abi_decoder_ids st.cs_next_id st'.cs_next_id SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `parent_site IN abi_decoder_ids first last /\
   ~(parent_site IN abi_decoder_ids st.cs_next_id st'.cs_next_id) /\
   FINITE (abi_decoder_ids st.cs_next_id st'.cs_next_id)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_child_excludes_ancestor >> disch_then assume_tac >>
  `mload parent_slot actual = mload parent_slot initial` by
    (drule_all abi_decode_footprint_frame_mload >> simp[]) >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `parent_site <> st.cs_next_id` by decide_tac >>
  `FLOOKUP actual.vs_allocas parent_site = SOME (parent_slot,32)` by
    (qpat_x_assum `!id. _` (qspec_then `parent_site` mp_tac) >> simp[]) >>
  `eval_operand parent_ptr actual = SOME (n2w parent_slot)` by
    (qpat_x_assum `!op. _` (qspec_then `parent_ptr` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live st'.cs_next_var parent_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  simp[abi_encoder_cursor_def] >> decide_tac
QED

Theorem abi_scratch_prefix_cursor:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
    limit_st first last b cap initial actual /\ first <= st.cs_next_id ==>
  ?slot. abi_encoder_cursor T dyn_ptr st.cs_next_id slot first st.cs_next_id st'
    (SUM (MAP (\(_,asz,_,_). asz) infos)) actual
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decoder_operand_live st'.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  qexists_tac `slot` >> gvs[abi_encoder_cursor_def]
QED
