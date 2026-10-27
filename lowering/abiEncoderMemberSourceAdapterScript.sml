(* Early source-contract interpretation of the common member engine. *)
Theory abiEncoderMemberSourceAdapter
Ancestors
  abiEncoderMemberSpine abiEncoderMemberSourcePhase abiEncoderStatic abiEncoderAddressReach
  abiEncoderMemberPhaseRaw abiDecoderDynamicLoopSetup abiDecoderArrayInitExec
  abiEncoderChildFrames abiEncoderCorrect abiEncoderChildInputs abiDecoderEffect
  abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec compileEnv
  valueEncoding venomState words list arithmetic

Theorem abi_encoder_static_child_spine_reach:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_context >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id /\
   st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  `abi_encoder_spine_core_code func (ei,head,src,prepared,end_st,out)` by
    fs[abi_encoder_spine_core_code_def] >>
  qabbrev_tac `Pre = \(e,dd,ss,p,en,op:operand) s.
    abi_encoder_correct e /\ abi_encoder_pre e at av p ss dd sb source_cap (d+offset) b cap s /\
    abi_decoder_budget first last b cap s /\ first <= p.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = p.cs_current_bb /\ s.vs_inst_idx = LENGTH p.cs_current_insts` >>
  qabbrev_tac `Post = \(e:abi_enc_info,dd:operand,ss:operand,p,en,op) s t.
    mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand op t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
      limit_st (d+offset) (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t` >>
  `!c r. abi_encoder_spine_core_code func c /\ Pre c r ==>
    ?t. Post c r t /\ Post c r t` by
    (rpt gen_tac >> PairCases_on `c` >>
     simp_tac (srw_ss()) [Abbr `Pre`, Abbr `Post`, abi_encoder_spine_core_code_def] >>
     rpt strip_tac >> irule abi_encoder_correct_run >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  `!r. abi_encoder_member_phase_raw st prepared initial r ==>
    Pre (ei,head,src,prepared,end_st,out) r` by
    (rpt strip_tac >> drule_all abi_encoder_member_static_place_raw_transport >> strip_tac >>
     `abi_decoder_budget first last b cap r` by
       (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `r:venom_state`]
         abi_decoder_budget_transport) >> fs[abi_decoder_address_frame_def]) >>
     drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >>
     strip_tac >> fs[Abbr `Pre`]) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  drule_all abi_encoder_spine_static_run >>
  disch_then (qspec_then `dyn_ptr` strip_assume_tac) >>
  qpat_x_assum `Post _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `Post`] >> strip_tac >>
  rename1 `abi_decode_sim ctx func r t` >>
  qpat_x_assum `abi_encoder_spine_child _ _ _ _` kall_tac >>
  qpat_x_assum `!c rr. _` kall_tac >>
  qpat_x_assum `!rr. _` kall_tac >>
  qpat_x_assum `Abbrev (Pre = _)` kall_tac >>
  drule_all abi_encoder_member_static_place_raw_transport >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `abi_decode_footprint_frame [(d+offset,LENGTH (enc at av));(b,cap)] initial t` by
    (irule abi_encoder_frame_after_address >>
     qexistsl_tac [`st.cs_next_var`, `r`] >> fs[abi_decoder_effect_def]) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial r` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap r t` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d+offset`, `end_st.cs_next_id`, `prepared.cs_next_id`,
       `prepared.cs_next_var`, `LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial t` by
    (irule abi_decoder_effect_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

(* This layer must remain available before all member execution owners. *)
val _ =
  if List.exists
       (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
       ["abiEncoderMemberSpineCompat", "abiEncoderMemberPhaseExec", "abiEncoderMember",
        "abiScratchMembers", "abiEncoderMembersCorrect", "abiEncoderComplexStatic"]
  then raise Fail "source adapter imports a member execution owner"
  else ();

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_static_child_spine_reach) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "ENCODER_SOURCE_ADAPTER_AUDIT_OK static_child_spine_reach\n"
    else raise Fail "source adapter admission dependency: static_child_spine_reach"
  end;
