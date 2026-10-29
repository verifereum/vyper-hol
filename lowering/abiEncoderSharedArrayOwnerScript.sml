(* Fixed-owner adapters for the single shared body execution callbacks. *)
Theory abiEncoderSharedArrayOwner
Ancestors
  abiEncoderSharedOwner abiEncoderSharedArrayBody abiEncoderSharedArrayRound
  abiEncoderSharedInputEffect abiEncoderArrayCursor abiScratchEffect
  abiEncoderRegisteredEffect abiEncoderSharedContract abiEncoderMembersDefs
  abiDecoderAllocation
  compileEnv venomState valueEncoding words list arithmetic

Theorem abi_encoder_shared_array_static_body_owner:
  abi_encoder_shared ei /\ abi_encoder_static_leaf ei /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (out,en) /\
  fn_has_code body_st en func /\
  owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
  abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st j initial /\
  abi_encoder_cursor F dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  j < LENGTH avs /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = body_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH body_st.cs_current_insts ==>
  ?actual.
    abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
      (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first site owner_st j actual /\
    abi_encoder_cursor F dp cursor_site cursor_slot first site owner_st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site en.cs_next_id owner_st.cs_next_var limit_st
      d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual /\
    actual.vs_current_bb = en.cs_current_bb /\
    actual.vs_inst_idx = LENGTH en.cs_current_insts /\ ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
     (body_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial` by
    (irule abi_encoder_shared_input_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_cursor T ip site slot first site body_st j initial` by
    (irule abi_encoder_cursor_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_cursor F dp cursor_site cursor_slot first site body_st
     (LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial` by
    (irule abi_encoder_cursor_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_encoder_shared_array_static_body >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz F,Array NONE ty,ListV avs)
     (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_owner >> metis_tac[]) >>
  `abi_encoder_cursor T ip site slot first site owner_st j actual` by
    (irule abi_encoder_cursor_owner >> metis_tac[]) >>
  `abi_encoder_cursor F dp cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual` by
    (irule abi_encoder_cursor_owner >> metis_tac[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_encoder_shared_array_dynamic_body_owner:
  abi_encoder_shared ei /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (out,en) /\
  fn_has_code body_st en func /\
  owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
  abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st j initial /\
  abi_encoder_cursor T dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial /\
  site < cursor_site /\ j < LENGTH avs /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = body_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH body_st.cs_current_insts ==>
  ?actual.
    abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
      (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first site owner_st j actual /\
    abi_encoder_cursor T dp cursor_site cursor_slot first site owner_st
      (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last site en.cs_next_id owner_st.cs_next_var limit_st
      d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual /\
    actual.vs_current_bb = en.cs_current_bb /\
    actual.vs_inst_idx = LENGTH en.cs_current_insts /\ ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
     (body_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial` by
    (irule abi_encoder_shared_input_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_cursor T ip site slot first site body_st j initial` by
    (irule abi_encoder_cursor_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_cursor T dp cursor_site cursor_slot first site body_st
     (LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) initial` by
    (irule abi_encoder_cursor_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_encoder_shared_array_dynamic_body >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz T,Array NONE ty,ListV avs)
     (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_owner >> metis_tac[]) >>
  `abi_encoder_cursor T ip site slot first site owner_st j actual` by
    (irule abi_encoder_cursor_owner >> metis_tac[]) >>
  `abi_encoder_cursor T dp cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual` by
    (irule abi_encoder_cursor_owner >> metis_tac[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_encoder_shared_array_owner_effects:
  abi_scratch_effect first last site en.cs_next_id owner_st.cs_next_var limit_st
    d sz b cap initial encoded /\
  abi_encoder_registered_effect (abi_decoder_ids site en.cs_next_id) [(d,sz)] initial encoded /\
  en.cs_next_id <= hi ==>
  abi_scratch_effect first last site hi owner_st.cs_next_var limit_st
    d sz b cap initial encoded /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] initial encoded
Proof
  strip_tac >> conj_tac
  >- (irule abi_scratch_effect_widen >>
      qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >>
  irule abi_encoder_registered_effect_enlarge >> goal_assum (drule_at Any) >>
  simp[pred_setTheory.SUBSET_DEF,abi_decoder_ids_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array owner admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_static_body_owner,
    abi_encoder_shared_array_dynamic_body_owner,abi_encoder_shared_array_owner_effects];
