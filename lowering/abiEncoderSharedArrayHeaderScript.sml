(* Concrete header observations and extension stability on both selected edges. *)
Theory abiEncoderSharedArrayHeader
Ancestors
  abiEncoderArrayHeader abiEncoderArrayHeaderFrame abiEncoderExtendSim abiEncoderVarTransport
  abiEncoderRegisteredEffect abiDecoderVarExtend execEquivParamDefs
  abiEncoderSharedArrayIndex abiEncoderSharedContract abiDecoderFootprint
  abiScratchAddress abiEncoderArrayCursor abiEncoderMembersDefs
  abiDecoderLoopRegisters abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderAllocation
  abiDecoderArrayBackedge
  abiDecoderLoop abiDecoderContract venomState venomExecSemantics venomMemDefs
  words list arithmetic

Theorem abi_encoder_array_header_extend_state:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras
    (jump_to label (abi_encode_array_header_state iv cmp done i n s))
    (jump_to label (abi_encode_array_header_state iv cmp done i n t))
Proof
  strip_tac >>
  `abi_decoder_vars_extend extras (abi_encode_array_header_state iv cmp done i n s)
    (abi_encode_array_header_state iv cmp done i n t)` by
    (simp_tac bool_ss [abi_encode_array_header_state_def] >>
     rpt (irule abi_decoder_vars_extend_update) >> asm_rewrite_tac []) >>
  pop_assum mp_tac >>
  simp[abi_decoder_vars_extend_def, jump_to_def, vsr_frame_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encoder_array_header_extend_sim:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\ count_op <> Var iv /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  abi_encoder_extend_sim ctx func s (jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_encode_array_header_sim >> simp[]) >>
  rpt strip_tac >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  `eval_operand ip t = SOME p /\ eval_operand count_op t = SOME (n2w n)` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  `s.vs_memory = t.vs_memory` by
    fs[abi_decoder_vars_extend_def, vsr_frame_def, venom_state_component_equality,
      Excl "vsr_complete_mask_equality"] >>
  `mload (w2n p) t = n2w i` by fs[mload_def] >>
  qexists_tac `jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n t)` >> conj_tac
  >- (irule abi_encoder_array_header_extend_state >> asm_rewrite_tac []) >>
  gvs[] >>
  irule abi_encode_array_header_sim >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`count_op`,`id`,`ip`] >> simp[]
QED

Theorem abi_encoder_array_header_registered:
  abi_encoder_registered_effect ids outs s
    (jump_to label (abi_encode_array_header_state iv cmp done i n s)) /\
  (alloca_inv s ==> alloca_inv (jump_to label (abi_encode_array_header_state iv cmp done i n s)))
Proof
  simp[abi_encoder_registered_effect_def, jump_to_def, abi_encode_array_header_state_def,
    update_var_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_shared_input_address:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s /\
  abi_decoder_address_frame st.cs_next_var s t ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) t
Proof
  simp_tac bool_ss [abi_encoder_shared_input_def, abi_decoder_address_frame_def] >>
  strip_tac >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  fs[abi_decoder_child_scratch_def]
QED

Theorem abi_encoder_shared_array_index_address:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s /\
  abi_decoder_address_frame owner_st.cs_next_var s t /\
  fresh_vars_wrt limit_st t /\ hi <= last /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] s t /\
  (alloca_inv s ==> alloca_inv t) /\ abi_encoder_extend_sim ctx func s t /\
  t.vs_current_bb = next_label /\ t.vs_inst_idx = 0 ==>
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) next_label j origin t
Proof
  strip_tac >> drule abi_encoder_shared_array_index_facts >> strip_tac >>
  qpat_x_assum `active = is_dynamic ty` kall_tac >>
  qpat_x_assum `asz = abi_member_head_size ty` kall_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) t` by
    (drule_all abi_encoder_shared_input_address >> simp[]) >>
  `abi_encoder_cursor T ip site slot first site owner_st j t /\
   abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
     (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) t` by
    (conj_tac >> irule abi_encoder_cursor_address >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`s`,`owner_st`] >> full_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap s t` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ ~t.vs_halted` by fs[abi_decoder_address_frame_def] >>
  irule abi_encoder_shared_array_index_advance >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`s`,`j`,`label`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_header_index:
  lookup_block label func.fn_blocks = SOME <|bb_label := label; bb_instructions :=
    abi_encode_array_header_insts id ip count_op (STRING #"%" (toString owner_st.cs_next_var))
      (STRING #"%" (toString (owner_st.cs_next_var+1)))
      (STRING #"%" (toString (owner_st.cs_next_var+2))) body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  owner_st.cs_next_id <= last /\ owner_st.cs_next_var+3 <= limit_st.cs_next_var /\ hi <= last /\
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin s ==>
  ?t. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz)
    (if j < LENGTH avs then body_lbl else exit_lbl) j origin t /\
    abi_encoder_extend_sim ctx func s t
Proof
  strip_tac >> drule abi_encoder_shared_array_index_facts >> strip_tac >>
  qpat_x_assum `active = is_dynamic ty` kall_tac >>
  qpat_x_assum `asz = abi_member_head_size ty` kall_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  `count_op <> Var (STRING #"%" (toString owner_st.cs_next_var))` by
    (drule abi_decoder_live_excludes_output >> simp[]) >>
  qabbrev_tac `t = jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
    (abi_encode_array_header_state (STRING #"%" (toString owner_st.cs_next_var))
      (STRING #"%" (toString (owner_st.cs_next_var+1)))
      (STRING #"%" (toString (owner_st.cs_next_var+2))) j (LENGTH avs) s)` >>
  `abi_decoder_address_frame owner_st.cs_next_var s t` by
    simp[Abbr `t`, abi_encode_array_header_address_frame] >>
  `fresh_vars_wrt limit_st t` by
    (simp_tac bool_ss [Abbr `t`, abi_decoder_fresh_jump] >>
     irule abi_encode_array_header_registers >> simp[]) >>
  `abi_encoder_extend_sim ctx func s t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_encoder_array_header_extend_sim >>
     asm_simp_tac (srw_ss()) [] >>
     qexistsl_tac [`count_op`,`id`,`ip`,`n2w slot`] >>
     asm_simp_tac bool_ss [] >>
     drule_all abi_encoder_cursor_bounds >> strip_tac >>
     fs[abi_encoder_cursor_def, w2n_n2w]) >>
  `t.vs_current_bb = (if j < LENGTH avs then body_lbl else exit_lbl) /\ t.vs_inst_idx = 0` by
    simp[Abbr `t`, jump_to_def] >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_shared_array_index_address >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`label`,`s`] >> asm_simp_tac bool_ss [] >>
  simp[Abbr `t`, abi_encoder_array_header_registered, jump_to_def,
    abi_encode_array_header_state_def, update_var_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array header admission, axiom or hypothesis"
  end) [abi_encoder_array_header_extend_state, abi_encoder_array_header_extend_sim,
    abi_encoder_array_header_registered, abi_encoder_shared_input_address,
    abi_encoder_shared_array_index_address, abi_encoder_shared_array_header_index];
