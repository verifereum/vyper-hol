Theory exprSimAbiDecodePathLift
Ancestors
  abiEncoderVarTransport exprSimAbiDecodeStepLift abiEncoderObserver
  abiDecoderVarExtend abiDecoderVarSequence relation venomState venomInst
  venomExecSemantics

(* Successful observation steps, including PHI entry, already have a general
   transport interface. Only the rejecting endpoint needs a decoder opcode. *)
Theorem abi_decode_observer_rtc_extend:
  !s u. RTC (abi_observer_step ctx fn cut) s u ==>
  !s'. abi_decoder_vars_extend extras s s' ==>
  ?u'. RTC (abi_observer_step ctx fn cut) s' u' /\
    abi_decoder_vars_extend extras u u'
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (qexists_tac `s'` >> simp[]) >>
  drule_all abi_encoder_observer_step_extend >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[RTC_RULES]
QED

Theorem abi_decode_observer_reject_extend:
  RTC (abi_observer_step ctx fn cut) s u /\
  abi_decoder_vars_extend extras s s' /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst u = Abort Revert_abort v ==>
  ?u' v'. RTC (abi_observer_step ctx fn cut) s' u' /\
    lookup_block u'.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u'.vs_inst_idx = SOME inst /\
    step_inst_base inst u' = Abort Revert_abort v' /\
    abi_decoder_vars_extend extras u u' /\
    abi_decoder_vars_extend extras v v'
Proof
  strip_tac >> drule_all abi_decode_observer_rtc_extend >> strip_tac >>
  drule_all abi_decode_revert_vars_extend >> strip_tac >>
  qpat_assum `abi_decoder_vars_extend extras u u'`
    (strip_assume_tac o MATCH_MP abi_encoder_vars_extend_control) >>
  metis_tac[]
QED
