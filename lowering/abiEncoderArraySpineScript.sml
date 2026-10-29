(* One actual array-tail execution spine; interpretations supply only transport
   and the recursive child callback. The array prefix is not a member prefix. *)
Theory abiEncoderArraySpine
Ancestors
  abiEncoderMemberSpine abiEncoderMemberPhaseRaw abiEncoderArrayTail abiBuiltinPrefix
  abiDecoderFrame abiDecoderReentry abiDecoderDynamicLoopSetup instIdxIndep
  compileEnv venomState venomExecSemantics venomInstProps exprLoweringProps words list

Theorem abi_encoder_array_tail_raw_control:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  eval_operand data_op initial = SOME (n2w d) /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  ready.vs_current_bb = initial.vs_current_bb /\
  ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule_all abi_encoder_member_tail_transport >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def, abi_decoder_address_frame_def] >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts st prepared` >> asm_rewrite_tac [] >>
  rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED


Theorem abi_encoder_array_spine_dynamic_run:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  abi_encoder_spine_core_code func (ei,SND ops,src,prepared,child_end,child_len) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (out,end_st) /\
  eval_operand data_op initial = SOME (n2w d) /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!ready. abi_encoder_member_phase_raw st prepared initial ready ==>
    child_pre (ei,SND ops,src,prepared,child_end,child_len) ready) /\
  (!c ready. abi_encoder_spine_core_code func c /\ child_pre c ready ==>
    ?encoded. core_run c ready encoded /\ child_post c ready encoded) /\
  (!ready encoded. child_post (ei,SND ops,src,prepared,child_end,child_len) ready encoded ==>
    abi_encoder_spine_cursor_input
      (head,dyn_ptr,FST ops,child_len,child_end,end_st,limit_st) encoded) ==>
  ?ready encoded actual.
    abi_encoder_member_phase_raw st prepared initial ready /\
    abi_encoder_spine_call core_run (ei,SND ops,src,prepared,child_end,child_len) ready encoded /\
    child_post (ei,SND ops,src,prepared,child_end,child_len) ready encoded /\
    abi_encoder_member_phase_raw child_end end_st encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_tail_raw >> disch_then (qx_choose_then `ready` assume_tac) >>
  `child_pre (ei,SND ops,src,prepared,child_end,child_len) ready` by metis_tac[] >>
  qpat_x_assum `!c ready. _` (drule_all_then (qx_choose_then `encoded` strip_assume_tac)) >>
  `abi_encoder_spine_cursor_input
    (head,dyn_ptr,FST ops,child_len,child_end,end_st,limit_st) encoded` by metis_tac[] >>
  drule_all abi_encoder_spine_cursor_run >> disch_then (qx_choose_then `actual` assume_tac) >>
  qexistsl_tac [`ready`, `encoded`, `actual`] >>
  gvs[abi_encoder_spine_call_def, abi_encoder_spine_core_code_def]
QED
