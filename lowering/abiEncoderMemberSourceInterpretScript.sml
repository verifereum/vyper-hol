(* Pure source transport for generated child certificates. *)
Theory abiEncoderMemberSourceInterpret
Ancestors
  abiEncoderMemberSourceContract abiEncoderMemberSpine abiDecoderArrayInitExec
  abiEncoderChildSourcePhase abiEncoderChildContext
  abiEncoderAddressReach abiEncoderChildCompose abiEncoderChildFrames abiEncoderChildInputs
  abiEncoderMemberPhaseRaw abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_member_source_static_input:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_spine_child_input func limit_st
    (abi_encoder_member_core_pre (at,av,sb,source_cap,d+offset) (first,last,b,cap,limit_st))
    (abi_encoder_member_core_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id`
    by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  simp_tac bool_ss [abi_encoder_spine_child_input_def] >>
  qexistsl_tac [`head`, `prepared`, `n2w d`] >>
  asm_simp_tac bool_ss [abi_encoder_spine_core_code_def] >>
  rpt strip_tac >> drule_all abi_encoder_child_static_place_raw_transport >> strip_tac >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  `abi_decoder_budget first last b cap r` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `r:venom_state`]
      abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
  strip_tac >> fs[abi_encoder_member_core_pre_def]
QED

Theorem abi_encoder_member_source_static_output:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decoder_budget first last b cap initial /\
  abi_encoder_spine_child_output
    (abi_encoder_member_core_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial t ==>
  mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t /\
  abi_decoder_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial t /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def, abi_encoder_member_core_post_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[] >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `p.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= p.cs_next_var /\
    st.cs_next_id <= p.cs_next_id` by decide_tac >>
  drule_all abi_encoder_child_static_place_raw_transport >> strip_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t` by
    (irule abi_encoder_frame_after_address >>
     qexistsl_tac [`st.cs_next_var`, `r`] >> fs[abi_decoder_effect_def]) >>
  `abi_decoder_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial r` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st d output_size b cap r t` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d+offset`, `en.cs_next_id`, `p.cs_next_id`,
       `p.cs_next_var`, `LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial t` by
    (irule abi_decoder_effect_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  asm_rewrite_tac []
QED
