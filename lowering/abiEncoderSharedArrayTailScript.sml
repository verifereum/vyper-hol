(* Concrete rich array-tail reach, using the same neutral driver as both old
   window and physical-scratch wrappers. *)
Theory abiEncoderSharedArrayTail
Ancestors
  abiEncoderSharedArraySpine abiEncoderSharedMemberContract abiEncoderMemberSpineCompat
  abiEncoderArraySpine abiEncoderArrayTail abiEncoderMemberSpine abiEncoderMemberPhaseRaw
  abiEncoderSharedContract abiEncoderCounters abiEncoderChildCode abiEncoderChildSuffix
  abiDecoderContract abiDecoderDynamicLoopSetup abiDecoderReentry
  abiScratchMemberContract compileEnv venomState valueEncoding words list

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

(* Pure observations at the driver's actual suffix state.  The zero-byte
   branch deliberately needs no disjointness of the empty child window. *)
Theorem abi_encoder_shared_array_tail_observations:
  abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb:num,source_cap:num,q)
    (first,last,b,cap,limit_st) (head,offset,dp,h,off,slot,site)
    (ei:abi_enc_info,dst:operand,src:operand,p,ce,len) ready encoded /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\
  abi_encoder_member_phase_raw ce en encoded actual /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  en.cs_next_var <= limit_st.cs_next_var /\
  (h+32 <= slot \/ slot+32 <= h) /\
  (LENGTH (enc at av) = 0 \/
    ((q+LENGTH (enc at av) <= h \/ h+32 <= q) /\
     (q+LENGTH (enc at av) <= slot \/ slot+32 <= q))) ==>
  mem_bytes_at q (LENGTH (enc at av)) actual.vs_memory = enc at av /\
  mem_word_at h actual.vs_memory = n2w off /\
  mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
  fresh_vars_wrt limit_st actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_shared_member_dynamic_saved >> strip_tac >>
  `abi_encoder_spine_cursor_input (head,dp,offset,len,ce,en,limit_st) encoded` by
    (drule_all abi_encoder_shared_member_dynamic_cursor_input >> simp[]) >>
  `abi_decoder_operand_live ce.cs_next_var dp /\
   abi_decoder_operand_live ce.cs_next_var len` by fs[abi_encoder_spine_cursor_input_def] >>
  `eval_operand len encoded = SOME (n2w (LENGTH (enc at av)))` by
    fs[abi_encoder_shared_member_dynamic_post_def, abi_encoder_spine_shared_post_def,
       abi_encoder_shared_endpoint_def] >>
  drule_all abi_encoder_member_cursor_transport >> strip_tac >>
  `mem_bytes_at q (LENGTH (enc at av)) encoded.vs_memory = enc at av` by
    (fs[abi_encoder_shared_member_dynamic_post_def, abi_encoder_spine_shared_post_def] >>
     drule abi_encoder_shared_endpoint_bytes >> simp[]) >>
  `mem_bytes_at q (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (Cases_on `LENGTH (enc at av) = 0`
     >- (gvs[LENGTH_NIL] >> simp[mem_bytes_at_def]) >>
     `mem_bytes_at q (LENGTH (enc at av)) actual.vs_memory =
      mem_bytes_at q (LENGTH (enc at av)) encoded.vs_memory` by
       (qpat_assum `actual.vs_memory = _` (fn th => rewrite_tac [th]) >>
        irule abi_encoder_child_suffix_preserves_tail >> gvs[]) >>
     asm_rewrite_tac []) >>
  `mem_word_at h actual.vs_memory = n2w off /\
   mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av))` by
    (asm_rewrite_tac [] >> irule abi_encoder_child_suffix_words >> asm_rewrite_tac []) >>
  asm_rewrite_tac []
QED
