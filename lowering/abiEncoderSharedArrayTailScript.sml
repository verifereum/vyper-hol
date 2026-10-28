(* Concrete rich array-tail reach, using the same neutral driver as both old
   window and physical-scratch wrappers. *)
Theory abiEncoderSharedArrayTail
Ancestors
  abiEncoderSharedArraySpine abiEncoderSharedMemberContract abiEncoderMemberSpineCompat
  abiEncoderArraySpine abiEncoderArrayTail abiEncoderMemberSpine abiEncoderMemberPhaseRaw
  abiEncoderSharedContract abiEncoderCounters abiEncoderChildCode abiEncoderChildSuffix
  abiDecoderContract abiDecoderDynamicLoopSetup abiDecoderReentry
  abiScratchMemberContract compileEnv venomState words list

Theorem abi_encoder_shared_array_tail_reach:
  abi_encoder_shared ei /\
  abi_encode_array_tail data_op dp st = (ops,p) /\
  abi_encoder_spine_core_code func (ei,SND ops,src,p,ce,len) /\
  abi_encode_child_suffix head dp (FST ops) len ce = (out,en) /\
  abi_encoder_shared_input (ei,at,av) (st,src,data_op) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand head initial = SOME (n2w h) /\
  abi_decoder_operand_live st.cs_next_var head /\
  eval_operand dp initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dp /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\ h < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\
  first <= site /\ site < last /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ce.cs_next_id <= last /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb ==>
  ?ready encoded actual.
    abi_encoder_member_phase_raw st p initial ready /\
    abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (head,FST ops,dp,h,off,slot,site)
      (ei,SND ops,src,p,ce,len) ready encoded /\
    abi_encoder_member_phase_raw ce en encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  `p.cs_next_var <= ce.cs_next_var` by
    (fs[abi_encoder_spine_core_code_def] >> drule abi_encoder_counters >> simp[]) >>
  `p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
   first <= p.cs_next_id` by decide_tac >>
  `eval_operand data_op initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var data_op` by fs[abi_encoder_shared_input_def] >>
  `!ready. abi_encoder_member_phase_raw st p initial ready ==>
    abi_encoder_shared_member_dynamic_pre (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (head,FST ops,dp,h,off,slot,site)
      (ei,SND ops,src,p,ce,len) ready` by
    (rpt strip_tac >> simp_tac bool_ss [abi_encoder_shared_member_dynamic_pre_def] >>
     conj_tac
     >- (irule abi_encoder_array_spine_shared_pre >>
         goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
         qexistsl_tac [`data_op`,`dp`,`initial`,`output_size`,`slot`,`st`] >>
         asm_rewrite_tac []) >>
     irule abi_encoder_array_spine_cursor_saved >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     qexistsl_tac [`d`,`data_op`,`initial`,`st`] >> asm_rewrite_tac []) >>
  drule_all abi_encoder_array_spine_shared_run >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `ready` (qx_choose_then `encoded`
      (qx_choose_then `actual` strip_assume_tac)))) >>
  qexistsl_tac [`ready`,`encoded`,`actual`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array tail admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_tail_reach];
