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

Definition abi_encoder_ignored_inputs_def:
  abi_encoder_ignored_inputs opc <=>
    MEM opc [NOP; CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
      COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
      SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE]
End

Theorem abi_encoder_eval_operands_inputs:
  !ops ws. eval_operands ops s = SOME ws ==>
  !x. MEM (Var x) ops ==> IS_SOME (lookup_var x s)
Proof
  Induct >> simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operand_def] >> metis_tac[]
QED

Theorem abi_encoder_pure3_inputs:
  exec_pure3 f inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  rw[exec_pure3_def, abi_decoder_inputs_defined_def] >>
  gvs[AllCaseEqs()] >> gvs[eval_operand_def]
QED

Theorem abi_encoder_extract_labels_inputs:
  !ops labels. extract_labels ops = SOME labels ==>
  !x. ~MEM (Var x) ops
Proof
  Induct >> simp[extract_labels_def] >>
  Cases_on `h` >> simp[extract_labels_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_encoder_log_inputs[local]:
  2 <= LENGTH ops /\
  eval_operand (HD (REVERSE ops)) s = SOME off /\
  eval_operand (EL 1 (REVERSE ops)) s = SOME sz /\
  eval_operands (DROP 2 (REVERSE ops)) s = SOME topics /\
  MEM (Var x) ops ==> IS_SOME (lookup_var x s)
Proof
  strip_tac >>
  `MEM (Var x) (REVERSE ops)` by simp[] >>
  qpat_x_assum `MEM (Var x) ops` kall_tac >>
  qpat_x_assum `2 <= LENGTH ops` mp_tac >>
  `LENGTH (REVERSE ops) = LENGTH ops` by simp[] >>
  pop_assum (SUBST1_TAC o SYM) >>
  namedCases_on `REVERSE ops` ["", "first tail"] >> simp[] >>
  namedCases_on `tail` ["", "second rest"] >> simp[] >>
  gvs[] >> rpt strip_tac >> gvs[eval_operand_def] >>
  metis_tac[abi_encoder_eval_operands_inputs]
QED

Theorem abi_encoder_step_inputs_defined:
  ~abi_encoder_ignored_inputs inst.inst_opcode /\
  step_inst_base inst s = OK u ==> abi_decoder_inputs_defined inst s
Proof
  strip_tac >>
  Cases_on `abi_decoder_reentry_opcode inst.inst_opcode`
  >- metis_tac[abi_decoder_step_inputs_defined] >>
  Cases_on `inst.inst_opcode` >>
  gvs[abi_encoder_ignored_inputs_def, abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  rpt strip_tac >>
  FIRST_PROVE [
    drule abi_decoder_pure1_inputs >> simp[],
    drule abi_decoder_pure2_inputs >> simp[],
    drule abi_encoder_pure3_inputs >> simp[],
    drule abi_decoder_read1_inputs >> simp[],
    drule abi_decoder_write2_inputs >> simp[],
    (gvs[abi_decoder_inputs_defined_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[eval_operand_def] >>
     FIRST_PROVE [
       metis_tac[abi_encoder_extract_labels_inputs, abi_encoder_eval_operands_inputs],
       (rename1 `eval_operand (HD (REVERSE log_ops)) s = SOME log_off` >>
        rename1 `eval_operand (EL 1 (REVERSE log_ops)) s = SOME log_sz` >>
        rename1 `eval_operands (DROP 2 (REVERSE log_ops)) s = SOME log_topics` >>
        irule abi_encoder_log_inputs >>
        qexistsl_tac [`log_off`, `log_ops`, `log_sz`, `log_topics`] >> simp[])])]
QED
