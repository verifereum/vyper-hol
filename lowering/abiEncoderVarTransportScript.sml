(* Successful execution transport with bounded additional variable bindings. *)
Theory abiEncoderVarTransport
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend abiEncoderObserver
  execEquivParamDefs venomExecSemantics venomState list

Theorem abi_encoder_vars_extend_prev:
  abi_decoder_vars_extend extras s t ==> s.vs_prev_bb = t.vs_prev_bb
Proof
  rw[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  qpat_x_assum `vsr_frame s = vsr_frame t`
    (mp_tac o AP_TERM ``\s:venom_state. s.vs_prev_bb``) >>
  simp[vsr_frame_def]
QED

Theorem abi_encoder_one_phi_extend:
  abi_decoder_vars_extend extras s t /\ eval_one_phi s inst = SOME (out,v) ==>
  eval_one_phi t inst = SOME (out,v)
Proof
  strip_tac >> drule abi_encoder_vars_extend_prev >> strip_tac >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  drule_all abi_decoder_vars_extend_eval >> simp[]
QED

Theorem abi_encoder_phis_extend:
  !insts s t u.
  abi_decoder_vars_extend extras s t /\ eval_phis s insts = OK u ==>
  ?v. eval_phis t insts = OK v /\ abi_decoder_vars_extend extras u v
Proof
  Induct >- simp[eval_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[eval_phis_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      drule_all abi_encoder_one_phi_extend >> strip_tac >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      simp[eval_phis_def] >>
      irule abi_decoder_vars_extend_update >> simp[]) >>
  simp[eval_phis_def] >> metis_tac[]
QED
