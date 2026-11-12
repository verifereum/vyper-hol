Theory exprSimAbiDecodeObserverReject
Ancestors
  exprSimAbiDecodeObservedEndpoint exprSimAbiDecodeRejectTransport
  exprSimAbiGasBridge abiEncoderObserver abiDecoderVarExtend
  abiEncoderVarTransport fragExec venomExecSemantics venomInst venomState relation list

Theorem abi_decode_frag_observer_cut_no_revert:
  (s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut sb ==>
  run_from fuel ctx (frag_observer sa sb fn id) s <> Abort Revert_abort v
Proof
  simp[frag_observer_cut_def] >> strip_tac >>
  simp[Once run_from_def, frag_observer_cut_lookup,
    Once exec_block_def, frag_observer_cut_instruction,
    get_instruction_def, EL_APPEND_EQN, step_inst_non_invoke,
    mk_inst_def, step_inst_base_opcode_eqs]
QED

Theorem abi_decode_frag_observer_reject_endpoint:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v ==>
  ?u bb inst.
    RTC (abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb)) s u /\
    (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region sa sb /\
    (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\ ~u.vs_halted /\
    lookup_block u.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst u = Abort Revert_abort v
Proof
  strip_tac >> irule abi_decode_reject_endpoint >>
  goal_assum (drule_at Any) >>
  simp[abi_decode_frag_observer_cut_no_revert] >>
  conj_tac >- metis_tac[frag_observer_off_cut_opcodes] >>
  conj_tac >- metis_tac[abi_decode_frag_observer_cut_no_revert] >>
  conj_tac >- metis_tac[frag_observer_start_region] >>
  metis_tac[frag_observer_region_closed]
QED

Theorem abi_decode_frag_observer_reject_lift:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v /\
  abi_decoder_vars_extend extras s s' ==>
  ?u' bb inst v'.
    RTC (abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb)) s' u' /\
    (u'.vs_current_bb,u'.vs_inst_idx) IN frag_observer_region sa sb /\
    (u'.vs_current_bb,u'.vs_inst_idx) <> frag_observer_cut sb /\ ~u'.vs_halted /\
    lookup_block u'.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
    get_instruction bb u'.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst u' = Abort Revert_abort v' /\
    abi_decoder_vars_extend extras v v'
Proof
  strip_tac >> drule_all abi_decode_frag_observer_reject_endpoint >> strip_tac >>
  drule_all abi_decode_observer_noninvoke_reject_extend >> strip_tac >>
  qpat_assum `abi_decoder_vars_extend extras u u'`
    (mp_then Any strip_assume_tac abi_encoder_vars_extend_control) >>
  metis_tac[]
QED
