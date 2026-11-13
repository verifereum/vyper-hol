Theory exprSimAbiDecodeStepLift
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend abiDecoderReentry abiEncoderObserver
  execEquivParamDefs venomExecSemantics venomState venomInst list

Theorem abi_decode_reentry_abort_shape:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  inst.inst_opcode = ASSERT /\
  ?op. inst.inst_operands = [op] /\ eval_operand op s = SOME 0w /\
    u = revert_state (set_returndata [] s)
Proof
  Cases_on `inst.inst_opcode` >>
  simp[abi_decoder_reentry_opcode_def] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = Abort Revert_abort u` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_alloca_def, exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem abi_decode_vars_extend_control:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras
    (s with <|vs_current_bb := bb; vs_prev_bb := prev; vs_inst_idx := idx|>)
    (t with <|vs_current_bb := bb; vs_prev_bb := prev; vs_inst_idx := idx|>)
Proof
  simp[abi_decoder_vars_extend_def, vsr_frame_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decode_vars_extend_stop:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (stop_view s) (stop_view t)
Proof
  simp[abi_decoder_vars_extend_def, vsr_frame_def, stop_view_def,
    halt_state_def, venom_state_component_equality,
    Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decode_revert_vars_extend:
  abi_decoder_vars_extend extras s t /\
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  ?v. step_inst_base inst t = Abort Revert_abort v /\
    abi_decoder_vars_extend extras u v
Proof
  strip_tac >> drule_all abi_decode_reentry_abort_shape >> strip_tac >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  qexists_tac `revert_state (set_returndata [] t)` >> conj_tac
  >- simp[Once step_inst_base_def] >>
  gvs[abi_decoder_vars_extend_def, vsr_frame_def, revert_state_def,
    set_returndata_def, venom_state_component_equality,
    Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decode_live_frame_lift:
  abi_decoder_vars_extend s.vs_vars u v /\
  (!op w. abi_decoder_operand_live next op /\
    eval_operand op (abi_decoder_prune_vars next s) = SOME w ==>
    eval_operand op u = SOME w) ==>
  !op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op v = SOME w
Proof
  rpt strip_tac >>
  metis_tac[abi_decoder_prune_eval, abi_decoder_vars_extend_eval]
QED
