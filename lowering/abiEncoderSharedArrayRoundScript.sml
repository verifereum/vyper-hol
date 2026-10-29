(* Body-to-next-index composition.  The body callback supplies its rich
   observations; the existing concrete backedge is the sole execution owner. *)
Theory abiEncoderSharedArrayRound
Ancestors
  abiEncoderSharedArrayBackedge abiEncoderSharedArrayHeader abiEncoderSharedArrayIndex
  abiEncoderRegisteredEffect abiEncoderExtendSim abiScratchEffect abiEncoderArrayCursor
  abiScratchEncoderContract abiEncoderMembersDefs abiDecoderAllocation
  abiDecoderContract abiDecoderReentry abiDecoderLoop compileEnv venomState
  valueEncoding words list arithmetic pred_set

Theorem abi_encoder_shared_array_round_finish:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) label j origin initial /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) encoded /\
  abi_encoder_array_prefix ty avs (SUC j) d encoded.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st j encoded /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) encoded /\
  abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial encoded /\
  abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] initial encoded /\
  (alloca_inv initial ==> alloca_inv encoded) /\ abi_encoder_extend_sim ctx func initial encoded /\
  lookup_block encoded.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  encoded.vs_inst_idx = LENGTH prefix /\ ~encoded.vs_halted /\
  eval_operand (Var iv) encoded = SOME (n2w j) /\ j < LENGTH avs /\
  owner_st.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  owner_st.cs_next_id <= last /\ site < hi /\ hi <= last /\
  (active ==> site < cursor_site /\ cursor_site < last) ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) hdr (SUC j) origin actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt limit_st encoded /\ abi_decoder_budget first last b cap encoded` by
    fs[abi_scratch_effect_def] >>
  `site < last` by decide_tac >>
  drule_all abi_encoder_shared_array_backedge_memory >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `first <= site` by fs[abi_encoder_cursor_def] >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap encoded actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`site+1`,`site`,`owner_st.cs_next_var`,`sz`] >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] encoded actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`abi_decoder_ids site (site+1)`,`[(d,sz)]`] >>
     simp[SUBSET_DEF,abi_decoder_ids_def]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `encoded` >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >> simp[]) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `encoded` >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_shared_array_index_advance >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`initial`,`j`,`label`] >> asm_simp_tac bool_ss [] >> metis_tac[]
QED
