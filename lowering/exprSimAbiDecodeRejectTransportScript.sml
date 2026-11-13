Theory exprSimAbiDecodeRejectTransport
Ancestors
  exprSimAbiDecodeStepLift exprSimAbiDecodePathLift opcodeClass
  abiEncoderVarTransport abiEncoderObserver relation
  abiDecoderVarExtend abiDecoderReentry abiDecoderVarSequence execEquivParamDefs venomExecSemantics venomState venomInst list

Theorem abi_decode_revert_opcode:
  step_inst_base inst s = Abort Revert_abort u ==>
  inst.inst_opcode = ASSERT \/ inst.inst_opcode = REVERT
Proof
  strip_tac >> drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[] >>
  qpat_x_assum `step_inst_base inst s = Abort Revert_abort u` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_create_abort_iff, exec_write2_def, exec_ext_call_def, AllCaseEqs()]
QED

Theorem abi_decode_noninvoke_revert_vars_extend:
  abi_decoder_vars_extend extras s t /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v /\
    abi_decoder_vars_extend extras u v
Proof
  strip_tac >> drule abi_decode_revert_opcode >> strip_tac
  >- (irule abi_decode_revert_vars_extend >>
      simp[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[Once step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >>
  imp_res_tac abi_decoder_vars_extend_eval >>
  qexists_tac `revert_state (set_returndata
    (TAKE (w2n sz) (DROP (w2n off) t.vs_memory ++ REPLICATE (w2n sz) 0w)) t)` >>
  conj_tac
  >- simp[Once step_inst_base_def] >>
  gvs[abi_decoder_vars_extend_def, vsr_frame_def, revert_state_def,
    set_returndata_def, venom_state_component_equality,
    Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decode_observer_noninvoke_reject_extend:
  RTC (abi_observer_step ctx fn cut) s u /\
  abi_decoder_vars_extend extras s s' /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\
  step_inst_base inst u = Abort Revert_abort v ==>
  ?u' v'. RTC (abi_observer_step ctx fn cut) s' u' /\
    lookup_block u'.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u'.vs_inst_idx = SOME inst /\
    step_inst_base inst u' = Abort Revert_abort v' /\
    abi_decoder_vars_extend extras u u' /\
    abi_decoder_vars_extend extras v v'
Proof
  strip_tac >> drule_all abi_decode_observer_rtc_extend >> strip_tac >>
  drule_all abi_decode_noninvoke_revert_vars_extend >> strip_tac >>
  qpat_assum `abi_decoder_vars_extend extras u u'`
    (mp_then Any strip_assume_tac abi_encoder_vars_extend_control) >>
  metis_tac[]
QED
