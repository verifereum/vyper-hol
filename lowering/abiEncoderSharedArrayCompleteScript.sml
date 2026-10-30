(* Read-only exit assembly at the existing scalar sequence endpoint. *)
Theory abiEncoderSharedArrayComplete
Ancestors
  abiEncoderSharedArrayExit abiEncoderArrayExit abiEncoderArrayScalarCode abiEncoderMemberPhaseRaw
  abiBuiltinPrefix abiEncoderRegisteredEffect abiEncoderExtendSim abiScratchEffect
  abiEncoderSharedArrayIndex abiEncoderSharedArrayInput abiEncoderSharedContract
  abiEncoderArrayCursor abiEncoderMembersDefs abiScratchEncoderContract
  valueEncodingProps abiDecodeRanges
  abiDecoderContract abiDecoderReentry compileEnv valueEncoding contractABI venomState venomMemDefs
  words list arithmetic

Theorem abi_encoder_shared_array_exit_run:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\
  (active ==> eval_operand dp initial = SOME (n2w slot) /\
    abi_decoder_operand_live st.cs_next_var dp /\ mload slot initial = n2w off /\
    slot < dimword (:256)) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (32+if active then off else cnt*asz)) /\
    actual.vs_memory = initial.vs_memory /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >>
  `?actual. abi_encoder_member_phase_raw st final initial actual` by
    (Cases_on `active` >> gvs[]
     >- (drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
         qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
         gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
         goal_assum (drule_at Any) >> simp[]) >>
     drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
     qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
     gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand out actual = SOME (n2w (32+if active then off else cnt*asz)) /\
   fresh_vars_wrt limit_st actual /\
   abi_decoder_address_frame st.cs_next_var initial actual /\
   actual.vs_current_bb = initial.vs_current_bb /\
   actual.vs_inst_idx = LENGTH final.cs_current_insts /\
   actual.vs_halted = initial.vs_halted` by
    (Cases_on `active` >> gvs[]
     >- (drule_all abi_encoder_array_dynamic_exit_raw_transport >> simp[]) >>
     drule_all abi_encoder_array_static_exit_raw_transport >> simp[]) >>
  drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  drule_all abi_encoder_array_exit_effect >>
  disch_then (qspecl_then [`sz`,`lo`,`hi`,`d`,`ctx`] strip_assume_tac) >>
  `st.cs_current_bb = final.cs_current_bb` by
    (Cases_on `active` >> gvs[]
     >- (drule (CONJUNCT2 abi_encode_array_exit_shape) >> simp[]) >>
     drule (CONJUNCT1 abi_encode_array_exit_shape) >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_array_index_exit_run:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) st.cs_current_bb (LENGTH avs) origin initial /\
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ LENGTH st.cs_current_insts = 0 /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_array_index_exit_facts >> strip_tac >>
  drule abi_encoder_shared_array_index_facts >> strip_tac >>
  drule abi_encoder_shared_array_index_layout >> strip_tac >>
  qpat_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  drule abi_encoder_shared_array_input_facts >> strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `sb < dimword (:256) /\ mload sb initial = n2w (LENGTH avs)` by
    (gvs[mem_word_at_eq_mload] >> decide_tac) >>
  `active ==> eval_operand dp initial = SOME (n2w cursor_slot) /\
    abi_decoder_operand_live st.cs_next_var dp /\
    mload cursor_slot initial = n2w (LENGTH (enc (Array NONE ty) (ListV avs))-32) /\
    cursor_slot < dimword (:256)` by
    (strip_tac >>
     `abi_encoder_cursor T dp cursor_site cursor_slot first site owner_st
       (LENGTH (enc (Array NONE ty) (ListV avs))-32) initial` by fs[] >>
     drule_all (Q.INST [`cursor_op` |-> `dp`] abi_encoder_cursor_bounds) >> strip_tac >>
     fs[abi_encoder_cursor_def, Excl "enc_def"] >>
     irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
   (active = F ==> LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*asz)` by
    (conj_tac >- decide_tac >> strip_tac >>
     `~is_dynamic ty` by metis_tac[] >>
     `!xs. SUM (MAP (abi_member_tail_size ty) xs) = 0` by
       (Induct >> simp[abi_member_tail_size_def]) >>
     fs[Excl "enc_def"]) >>
  `initial.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all abi_encoder_shared_array_exit_run >>
  disch_then (qspecl_then [`sz`,`lo`,`hi`,`d`,`ctx`] (qx_choose_then `actual` strip_assume_tac)) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  Cases_on `active` >> gvs[Excl "enc_def"]
QED

Theorem abi_encoder_shared_array_index_complete:
  abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) st.cs_current_bb (LENGTH avs) origin initial /\
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ LENGTH st.cs_current_insts = 0 /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= last /\ hi <= last /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap origin actual /\
    abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] origin actual /\
    (alloca_inv origin ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func origin actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_index_exit_run >>
  disch_then (qspec_then `site` (qx_choose_then `actual` strip_assume_tac)) >>
  drule abi_encoder_shared_array_index_facts >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_array_index _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_array_index_def]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial actual` by
    (irule abi_scratch_effect_widen >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap origin actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `initial` >> asm_rewrite_tac []) >>
  `abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] origin actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `initial` >> asm_rewrite_tac []) >>
  `abi_encoder_extend_sim ctx func origin actual` by
    (irule abi_encoder_extend_sim_trans >> qexists_tac `initial` >> asm_rewrite_tac []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
