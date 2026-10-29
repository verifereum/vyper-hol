(* Open array count preparation, reusing the actual count-copy sequence. *)
Theory abiEncoderSharedArrayCountPrepare
Ancestors
  abiEncoderSharedArrayCount abiEncoderSharedArrayInput abiEncoderSharedContract
  abiEncoderArrayCount abiEncoderArrayPrefix abiEncoderMemberPhaseRaw abiEncoderSequence
  abiDecoderArrayHeader abiDecoderGuards abiDecoderArrayLoopInit
  abiScratchEffect abiScratchEncoderContract abiEncoderRegisteredEffect abiEncoderExtendSim
  abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv
  venomState venomInst instIdxIndep valueEncoding words list arithmetic

Theorem abi_encoder_shared_array_count_prepare:
  abi_decode_array_header dst src MLOAD st = (cnt,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
      (prepared,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_decoder_operand_live prepared.cs_next_var cnt /\ eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encoder_shared_array_count_input_facts >> strip_tac >>
  `eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var dst` by fs[abi_encoder_shared_input_def] >>
  drule_all abi_encoder_array_count_copy_sequence >> disch_then (qx_choose_then `raw` strip_assume_tac) >>
  qabbrev_tac `actual = raw with vs_inst_idx := LENGTH prepared.cs_current_insts` >>
  `abi_encoder_member_phase_raw st prepared initial actual` by
    (simp[abi_encoder_member_phase_raw_def, Abbr `actual`] >> qexists_tac `raw` >> simp[]) >>
  drule_all abi_encoder_shared_array_count_input >> strip_tac >>
  drule_all abi_encoder_shared_array_count_effect >>
  disch_then (qspecl_then [`lo`,`hi`,`ctx`] strip_assume_tac) >>
  `actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts` by
    (drule (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
     simp[abi_decode_source_opcode_def, EVERY_CONJ] >> strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st prepared)` by
       fs[EVERY_CONJ] >>
     drule_all abi_encoder_run_sequence_reach >>
     disch_then (qspec_then `ctx` (qx_choose_then `endpoint` strip_assume_tac)) >>
     gvs[Abbr `actual`]) >>
  qexists_tac `actual` >> simp[Abbr `actual`]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared count preparation admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_count_prepare];
