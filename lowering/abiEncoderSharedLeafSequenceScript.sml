(* Common straight-line endpoint: reuse the successful concrete execution. *)
Theory abiEncoderSharedLeafSequence
Ancestors
  abiEncoderSharedContract abiEncoderSequence abiScratchLeafEffect abiScratchEncoderContract
  abiEncoderExtendSim abiDecoderContract abiEncoderRegisteredEffect
  abiDecoderFrame venomMemDefs venomState venomExecSemantics instIdxIndep
  valueEncoding list arithmetic

Theorem abi_encoder_sequence_post_registered:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
  actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests ==>
  abi_encoder_registered_effect ids [(d,LENGTH (enc at av))] initial actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def, abi_decode_frame_def,
    abi_encoder_registered_effect_def] >> strip_tac >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem abi_encoder_sequence_post_alloca_inv:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  alloca_inv initial ==> alloca_inv actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def] >> strip_tac >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encoder_shared_leaf_sequence:
  end_st.cs_blocks = start.cs_blocks /\ end_st.cs_current_bb = start.cs_current_bb /\
  inst_extends start end_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start end_st) /\
  run_inst_seq (emitted_insts start end_st) initial = OK raw /\
  abi_encoder_sequence_post at av out start limit_st d initial raw /\
  raw.vs_accounts = initial.vs_accounts /\ raw.vs_transient = initial.vs_transient /\
  raw.vs_logs = initial.vs_logs /\ raw.vs_requests = initial.vs_requests /\
  fn_has_code start end_st func /\ abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    (first,last,b,cap) (at,av,d) initial
    (raw with vs_inst_idx := LENGTH end_st.cs_current_insts)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[] >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial raw` by
    (irule abi_scratch_sequence_post_effect >> simp[] >> qexists_tac `out` >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
    [(d,LENGTH (enc at av))] initial raw` by
    (irule abi_encoder_sequence_post_registered >> simp[] >>
     qexistsl_tac [`limit_st`, `out`, `start`] >> simp[]) >>
  `(alloca_inv initial ==> alloca_inv raw)` by
    (metis_tac[abi_encoder_sequence_post_alloca_inv]) >>
  fs[abi_encoder_shared_endpoint_def, abi_encoder_sequence_post_def,
    abi_scratch_effect_def, abi_encoder_registered_effect_def,
    eval_op_inst_idx, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def] >> metis_tac[]
QED
