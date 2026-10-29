(* Fixed-origin rich ledger for both generated array loops. No execution recursion. *)
Theory abiEncoderSharedArrayIndex
Ancestors
  abiEncoderSharedArrayInput abiEncoderSharedContract abiEncoderRegisteredEffect abiEncoderExtendSim
  abiEncoderArrayPrefix abiEncoderMembersDefs abiScratchEffect abiScratchEncoderContract
  abiScratchDecoderLoopControl
  abiDecoderDynamicLoopSetup abiEncoderOpenInput
  abiDecoderContract abiDecoderReentry compileEnv valueEncoding contractABI venomState list arithmetic

Definition abi_encoder_shared_array_index_def:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s <=>
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st j s /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) s /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op s = SOME (n2w (LENGTH avs)) /\
  s.vs_current_bb = label /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap origin s /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] origin s /\
  (alloca_inv origin ==> alloca_inv s) /\ abi_encoder_extend_sim ctx func origin s
End

Theorem abi_encoder_shared_array_index_initial:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  mem_word_at d initial.vs_memory = n2w (LENGTH avs) /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  initial.vs_current_bb = label /\ initial.vs_inst_idx = 0 /\ ~initial.vs_halted /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label 0 initial initial
Proof
  strip_tac >>
  simp[abi_encoder_shared_array_index_def, abi_encoder_array_prefix_empty,
    abi_scratch_effect_refl, abi_encoder_registered_effect_refl, abi_encoder_extend_sim_refl]
QED

Theorem abi_encoder_shared_array_index_facts:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s ==>
  j <= LENGTH avs /\ LENGTH avs < dimword (:256) /\
  LIST_REL abi_encoder_structural_valid (REPLICATE (LENGTH avs) ty) avs /\
  asz = abi_member_head_size ty /\ active = is_dynamic ty /\
  first <= site /\ fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s
Proof
  simp_tac bool_ss [abi_encoder_shared_array_index_def] >> strip_tac >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  fs[abi_encoder_array_prefix_def, abi_encoder_cursor_def, abi_scratch_effect_def, Excl "enc_def"]
QED

Theorem abi_encoder_shared_array_index_advance:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin initial /\
  abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] initial actual /\
  (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
  abi_encoder_array_prefix ty avs k d actual.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st k actual /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE k avs))) actual /\
  hi <= last /\ actual.vs_current_bb = next_label /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted ==>
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) next_label k origin actual
Proof
  simp_tac bool_ss [abi_encoder_shared_array_index_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand count_op actual = SOME (n2w (LENGTH avs))` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `first <= site` by fs[abi_encoder_cursor_def] >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `initial` >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] origin actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `initial` >> simp[]) >>
  `abi_encoder_extend_sim ctx func origin actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_index_exit_facts:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label (LENGTH avs) origin s ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) s.vs_memory =
    enc (Array NONE ty) (ListV avs) /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH (enc (Array NONE ty) (ListV avs))-32) s
Proof
  strip_tac >> drule abi_encoder_shared_array_index_facts >> strip_tac >>
  drule abi_encoder_structural_list_layout >> disch_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  drule_all abi_encoder_open_array_prefix_complete >> disch_tac >>
  drule abi_encoder_open_array_length >> disch_tac >>
  `LENGTH (enc (Array NONE ty) (ListV avs))-32 =
    LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) avs)` by
    (full_simp_tac bool_ss [] >> decide_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [TAKE_LENGTH_ID]) >>
  gvs[Excl "enc_def"]
QED

Theorem abi_encoder_shared_array_index_layout:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s ==>
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) =
    32 + LENGTH avs*abi_member_head_size ty + SUM (MAP (abi_member_tail_size ty) avs)
Proof
  strip_tac >> drule abi_encoder_shared_array_index_facts >> strip_tac >>
  drule abi_encoder_structural_list_layout >> disch_tac >>
  asm_simp_tac bool_ss [abi_encoder_open_array_length]
QED

Theorem abi_encoder_shared_array_index_selected_input:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s /\
  j < LENGTH avs /\ LENGTH (enc ty (EL j avs)) <= sz /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  abi_decoder_operand_live owner_st.cs_next_var child_src ==>
  abi_encoder_shared_input (ei,ty,EL j avs) (owner_st,child_src,dst)
    (sb+32+j*msz,msz) (d,sz) (first,last,b,cap) s
Proof
  simp_tac bool_ss [abi_encoder_shared_array_index_def] >> strip_tac >>
  drule_all abi_encoder_shared_array_selected_input >> simp[]
QED
