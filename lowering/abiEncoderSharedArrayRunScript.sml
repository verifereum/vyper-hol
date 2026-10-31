(* Assembly of the generated loop from its prepared entry state. *)
Theory abiEncoderSharedArrayRun
Ancestors
  abiEncoderSharedArrayLoop abiEncoderSharedArrayEntry abiEncoderSharedArrayIndex
  abiEncoderSharedArrayEntry abiScratchEffect abiEncoderRegisteredEffect abiScratchEncoderContract
  abiEncoderSharedContract abiEncoderExtendSim abiEncoderArrayLoopCode
  abiEncoderArrayHeaderMemory abiEncoderMembersDefs abiDecoderContract abiDecoderReentry
  compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_shared_array_prepared_run:
  abi_encoder_shared ei /\
  ((active = F /\ abi_encoder_static_leaf ei /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (out,body_end)) \/
   (active = T /\
    abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (out,body_end))) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  mem_word_at d initial.vs_memory = n2w (LENGTH avs) /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  ?actual. abi_encoder_shared_array_index (ctx,func) (ei,asz,msz,active,ty,avs)
    (owner_st,limit_st,src,dst,ip,dp,count_op) (site,slot,cursor_site,cursor_slot)
    (first,last,hi,b,cap) (sb,source_cap,d,sz) (SND (SND labels)) (LENGTH avs) initial actual /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
      (LENGTH (enc (Array NONE ty) (ListV avs))-32) actual /\
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_loop_enter >>
  disch_then (qspecl_then [`hi`,`ctx`] strip_assume_tac) >>
  drule_all abi_encoder_shared_array_loop_run >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  drule abi_encoder_shared_array_index_exit_facts >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_extend_sim_trans >>
  qexists_tac `jump_to (FST labels) initial` >> asm_rewrite_tac []
QED

Theorem abi_encoder_shared_array_prepared_complete:
  abi_encoder_shared ei /\
  ((active = F /\ abi_encoder_static_leaf ei /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) \/
   (active = T /\
    abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end))) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st = (out,final)
   else abi_encode_array_static_exit src asz exit_st = (out,final)) /\
  fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (owner_st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  mem_word_at d initial.vs_memory = n2w (LENGTH avs) /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dp cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids site hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_shared_array_prepared_run >>
  disch_then (qspec_then `ctx` (qx_choose_then `encoded` strip_assume_tac)) >>
  `exit_st.cs_current_bb = SND (SND labels) /\ LENGTH exit_st.cs_current_insts = 0 /\
   owner_st.cs_next_var <= exit_st.cs_next_var /\ owner_st.cs_next_id <= last` by
    (fs[abi_encoder_array_loop_code_def] >> decide_tac) >>
  qpat_assum `exit_st.cs_current_bb = _`
    (fn th => RULE_ASSUM_TAC (PURE_ONCE_REWRITE_RULE [GSYM th])) >>
  drule_all abi_encoder_shared_array_index_complete >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
