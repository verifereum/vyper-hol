(* Successful execution transport with bounded additional variable bindings. *)
Theory abiEncoderVarTransport
Ancestors
  abiDecoderVarSequence abiDecoderVarExtend abiEncoderObserver
  execEquivParamDefs execEquivParamProps stateEquiv venomExecSemantics venomState list

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
  rpt gen_tac >> rename1 `eval_phis s (inst::rest) = OK u` >>
  Cases_on `inst.inst_opcode = PHI`
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
  Induct >- simp[extract_labels_def] >>
  qx_gen_tac `operand` >>
  simp[extract_labels_def] >>
  Cases_on `operand` >> simp[extract_labels_def, AllCaseEqs()] >>
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
  rpt strip_tac
  >>~- ([`exec_pure1 f inst s = OK u`],
        drule abi_decoder_pure1_inputs >> simp[])
  >>~- ([`exec_pure2 f inst s = OK u`],
        drule abi_decoder_pure2_inputs >> simp[])
  >>~- ([`exec_pure3 f inst s = OK u`],
        drule abi_encoder_pure3_inputs >> simp[])
  >>~- ([`exec_read1 f inst s = OK u`],
        drule abi_decoder_read1_inputs >> simp[])
  >>~- ([`exec_write2 f inst s = OK u`],
        drule abi_decoder_write2_inputs >> simp[]) >>
  gvs[abi_decoder_inputs_defined_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operand_def]
  >>~- ([`eval_operand (HD (REVERSE log_ops)) s = SOME log_off`],
        rename1 `eval_operand (EL 1 (REVERSE log_ops)) s = SOME log_sz` >>
        rename1 `eval_operands (DROP 2 (REVERSE log_ops)) s = SOME log_topics` >>
        irule abi_encoder_log_inputs >>
        qexistsl_tac [`log_off`, `log_ops`, `log_sz`, `log_topics`] >> simp[]) >>
  metis_tac[abi_encoder_extract_labels_inputs, abi_encoder_eval_operands_inputs]
QED

Theorem abi_encoder_step_extend_inputs[local]:
  abi_decoder_vars_extend extras s t /\ inst.inst_opcode <> INVOKE /\
  abi_decoder_inputs_defined inst s /\ step_inst_base inst s = OK u ==>
  ?v. step_inst_base inst t = OK v /\ abi_decoder_vars_extend extras u v
Proof
  strip_tac >>
  drule abi_decoder_vars_extend_inputs >> disch_then drule >> strip_tac >>
  mp_tac (Q.SPECL [`abi_decoder_vars_extend extras`,
    `\s t. vsr_term_frame s = vsr_term_frame t`, `0`, `ARB`, `inst`, `s`, `t`]
    execEquivParamPropsTheory.step_inst_preserves_R) >>
  impl_tac >- simp[abi_decoder_vars_extend_valid] >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
  Cases_on `step_inst_base inst t` >> simp[lift_result_def] >> metis_tac[]
QED

Theorem abi_encoder_vars_extend_frame[local]:
  abi_decoder_vars_extend extras s t ==>
  s.vs_memory = t.vs_memory /\ s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_tx_ctx = t.vs_tx_ctx /\ s.vs_block_ctx = t.vs_block_ctx /\
  s.vs_accounts = t.vs_accounts /\ s.vs_returndata = t.vs_returndata /\
  s.vs_code = t.vs_code
Proof
  rw[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  fs[vsr_frame_def, venom_state_component_equality]
QED

Theorem abi_encoder_step_extend_ignored[local]:
  abi_decoder_vars_extend extras s t /\ abi_encoder_ignored_inputs inst.inst_opcode /\
  step_inst_base inst s = OK u ==>
  ?v. step_inst_base inst t = OK v /\ abi_decoder_vars_extend extras u v
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_encoder_ignored_inputs_def] >>
  qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, exec_read0_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule abi_encoder_vars_extend_frame >> strip_tac >>
  asm_rewrite_tac[] >> irule abi_decoder_vars_extend_update >> simp[]
QED

Theorem abi_encoder_step_extend:
  abi_decoder_vars_extend extras s t /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK u ==>
  ?v. step_inst_base inst t = OK v /\ abi_decoder_vars_extend extras u v
Proof
  strip_tac >> Cases_on `abi_encoder_ignored_inputs inst.inst_opcode`
  >- (drule_all abi_encoder_step_extend_ignored >> simp[]) >>
  drule_all abi_encoder_step_inputs_defined >> strip_tac >>
  drule_all abi_encoder_step_extend_inputs >> simp[]
QED

Theorem abi_encoder_vars_extend_control:
  abi_decoder_vars_extend extras s t ==>
  s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
  s.vs_halted = t.vs_halted
Proof
  rw[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  fs[vsr_frame_def, venom_state_component_equality]
QED

Theorem abi_encoder_vars_extend_idx:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (s with vs_inst_idx := idx) (t with vs_inst_idx := idx)
Proof
  rw[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
  fs[vsr_frame_def, venom_state_component_equality]
QED

Theorem abi_encoder_observer_step_extend:
  abi_decoder_vars_extend extras s s' /\ abi_observer_step ctx fn cut s t ==>
  ?t'. abi_observer_step ctx fn cut s' t' /\ abi_decoder_vars_extend extras t t'
Proof
  rw[abi_observer_step_def] >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  gvs[step_inst_non_invoke] >>
  drule_all abi_encoder_step_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend extras middle extended` >>
  drule_all abi_encoder_vars_extend_control >> strip_tac
  >- (qexists_tac `extended with vs_inst_idx := SUC s'.vs_inst_idx` >>
      simp[] >> conj_tac >- metis_tac[] >>
      irule abi_encoder_vars_extend_idx >> simp[]) >>
  drule_all abi_encoder_phis_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend extras entered entered'` >>
  drule_all abi_encoder_vars_extend_control >> strip_tac >>
  qexists_tac `entered' with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  simp[] >> conj_tac
  >- metis_tac[] >>
  irule abi_encoder_vars_extend_idx >> simp[]
QED

Theorem abi_encoder_local_prefix_extend:
  local_prefix ctx fn cut s t ==>
  !s'. abi_decoder_vars_extend extras s s' ==>
  ?t'. local_prefix ctx fn cut s' t' /\ abi_decoder_vars_extend extras t t'
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (drule abi_encoder_vars_extend_control >> strip_tac >>
      qexists_tac `s'` >> simp[] >>
      irule (cj 1 local_prefix_rules) >> metis_tac[]) >>
  drule_all abi_encoder_observer_step_extend >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule (cj 2 local_prefix_rules) >> metis_tac[]
QED
