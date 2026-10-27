(* Early physical-scratch interpretation of the common member spine. *)
Theory abiScratchMemberAdapter
Ancestors
  abiEncoderMemberSpine abiEncoderMemberPhaseRaw abiEncoderMemberPhaseEffect
  abiScratchEncoderRun abiScratchChild abiScratchAfterAddress abiScratchAddress
  abiScratchEncoderContract abiScratchFootprint abiScratchEffect abiScratchFrameCompose
  abiEncoderChildContext abiEncoderAddressReach abiEncoderChildFrames abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI venomState
  pred_set words list arithmetic

Theorem abi_scratch_spine_frame_after_address:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo hi child_next limit_st d sz b cap ready actual /\
  lo <= child_lo ==>
  abi_decode_footprint_frame
    ([(d,sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual
Proof
  strip_tac >>
  `abi_decoder_ids child_lo hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_decode_footprint_frame
    ([(d,sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap ready) ready actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`,
       `child_ids` |-> `abi_decoder_ids child_lo hi`, `fp` |-> `[(d,sz)]`,
       `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_frame_subset_append) >>
     impl_tac >- (asm_simp_tac (srw_ss()) [] >> fs[abi_scratch_effect_def]) >> simp[]) >>
  drule_all abi_scratch_frame_after_address >> simp[]
QED

Theorem abi_scratch_static_child_spine_reach:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+offset) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame
      ([(d+offset,LENGTH (enc at av))] ++ abi_decoder_child_scratch
        (abi_decoder_ids st.cs_next_id end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id /\
   st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  `abi_encoder_spine_core_code func (ei,head,src,prepared,end_st,out)` by
    fs[abi_encoder_spine_core_code_def] >>
  qabbrev_tac `Pre = \(e,dd,ss,p,en,op:operand) s.
    abi_scratch_encoder e /\ abi_scratch_input e at av p ss dd sb source_cap (d+offset)
      (LENGTH (enc at av)) first last b cap s /\
    abi_decoder_budget first last b cap s /\ first <= p.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = p.cs_current_bb /\ s.vs_inst_idx = LENGTH p.cs_current_insts` >>
  qabbrev_tac `Post = \(e:abi_enc_info,dd:operand,ss:operand,p,en,op) s t.
    mem_bytes_at (d+offset) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand op t = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
      limit_st (d+offset) (LENGTH (enc at av)) b cap s t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t` >>
  `!c r. abi_encoder_spine_core_code func c /\ Pre c r ==>
    ?t. Post c r t /\ Post c r t` by
    (rpt gen_tac >> PairCases_on `c` >>
     simp_tac (srw_ss()) [Abbr `Pre`, Abbr `Post`, abi_encoder_spine_core_code_def] >>
     rpt strip_tac >> irule abi_scratch_encoder_run >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  `!r. abi_encoder_member_phase_raw st prepared initial r ==>
    Pre (ei,head,src,prepared,end_st,out) r` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
     `eval_operand head r = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
     mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
       `t` |-> `r:venom_state`, `ids` |-> `abi_decoder_ids first last`] abi_scratch_address) >>
     impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     `abi_scratch_input ei at av prepared src head sb source_cap (d+offset)
       (LENGTH (enc at av)) first last b cap r` by
       (mp_tac (Q.INST [`prepared` |-> `prepared:compile_state`, `actual` |-> `r:venom_state`,
          `child_dst` |-> `head:operand`, `off` |-> `offset:num`] abi_scratch_child_input_address) >>
        asm_simp_tac bool_ss [] >> decide_tac) >>
     fs[Abbr `Pre`]) >>
  drule_all abi_encoder_spine_static_run >>
  disch_then (qspec_then `dyn_ptr` strip_assume_tac) >>
  qpat_x_assum `Post _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `Post`] >> strip_tac >>
  rename1 `abi_decode_sim ctx func r t` >>
  qpat_x_assum `abi_encoder_spine_child _ _ _ _` kall_tac >>
  qpat_x_assum `!c rr. _` kall_tac >> qpat_x_assum `!rr. _` kall_tac >>
  qpat_x_assum `Abbrev (Pre = _)` kall_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `st.cs_next_id <= prepared.cs_next_id /\ end_st.cs_next_id <= end_st.cs_next_id /\
    d <= d+offset /\ (d+offset)+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  drule_all abi_scratch_spine_frame_after_address >> disch_tac >>
  drule_all (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `d` |-> `d:num`, `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >> disch_tac >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  qexists_tac `t` >> fs[]
QED

val _ =
  if List.exists
       (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
       ["abiEncoderStatic", "abiEncoderDynamic", "abiEncoderMemberSourcePhase", "abiEncoderMembersDefs",
        "abiEncoderMember", "abiEncoderMembersCorrect", "abiEncoderComplexStatic",
        "abiEncoderMemberSpineCompat", "abiEncoderMemberPhaseExec", "abiScratchStatic",
        "abiScratchDynamic", "abiScratchMemberStep", "abiScratchMembers", "abiScratchComplex"]
  then raise Fail "scratch adapter imports a member execution owner"
  else ();

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SCRATCH_ADAPTER_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("scratch adapter admission dependency: " ^ name)
  end)
  [("frame_after_address", abi_scratch_spine_frame_after_address),
   ("static_child_spine_reach", abi_scratch_static_child_spine_reach)];
