(* Pointer checks and ghost updates under defined-input extension. *)
Theory abiDecodePtrReentryStep
Ancestors
  abiDecodePtrReentryObservations abiDecoderVarSequence abiDecoderVarExtend
  ptrSafeRun ptrDiscipline contextCodegenRel codegenRel venomExecSemantics
  venomState venomInst list

Theorem abi_decode_ptr_reentry_access:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  (access_ok lo G fn inst s <=> access_ok lo G fn inst t)
Proof
  strip_tac >>
  drule abi_decode_ptr_reentry_eval >> disch_then drule >> strip_tac >>
  drule_all abi_decode_ptr_reentry_read_ranges >> strip_tac >>
  drule_all abi_decode_ptr_reentry_write_ranges >> strip_tac >>
  drule abi_decode_ptr_reentry_revert >> strip_tac >>
  simp[access_ok_def] >> metis_tac[MEM]
QED

Theorem abi_decode_ptr_reentry_taint_ok:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s ==>
  (taint_ok fn tn inst s <=> taint_ok fn tn inst t)
Proof
  strip_tac >>
  drule_all abi_decode_ptr_reentry_read_ranges >> strip_tac >>
  drule abi_decode_ptr_reentry_revert >> strip_tac >> simp[taint_ok_def]
QED

Theorem abi_decode_ptr_reentry_prov:
  abi_decoder_vars_extend extras u v /\ abi_decoder_reentry_opcode inst.inst_opcode ==>
  step_prov PG G inst u = step_prov PG G inst v
Proof
  strip_tac >> drule abi_decoder_vars_extend_observations >> strip_tac >>
  fs[abi_decoder_reentry_opcode_def] >>
  simp[step_prov_def, out_prov_def]
QED

Theorem abi_decode_ptr_reentry_taint:
  abi_decoder_vars_extend extras s t /\ abi_decoder_inputs_defined inst s /\
  abi_decoder_vars_extend more u v /\ abi_decoder_reentry_opcode inst.inst_opcode ==>
  step_taint inst s u tn = step_taint inst t v tn
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t`
    by metis_tac[abi_decode_ptr_reentry_eval] >>
  drule_all abi_decode_ptr_reentry_write_ranges >> strip_tac >>
  `new_site_bytes s u = new_site_bytes t v`
    by metis_tac[abi_decode_ptr_reentry_new_site] >>
  fs[abi_decoder_reentry_opcode_def] >>
  simp[step_taint_def, mem_taint_def, step_writes_def, adopt_reset_def,
       store_taint_def, imm_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >>
  gvs[written_taint_def, out_taint_def] >>
  namedCases_on `rest` ["", "b tail"] >>
  gvs[written_taint_def, out_taint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `tail` ["", "c ending"] >>
  gvs[written_taint_def, out_taint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `ending` >>
  gvs[written_taint_def, out_taint_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem abi_decode_ptr_reentry_check_frame[local]:
  abi_decoder_vars_extend extras s t ==>
  s.vs_requests = t.vs_requests /\ s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_allocas = t.vs_allocas /\ s.vs_initial_fmp = t.vs_initial_fmp /\
  s.vs_fmp = t.vs_fmp
Proof
  strip_tac >> drule abi_decoder_vars_extend_restore >>
  disch_then (mp_tac o AP_TERM ``\z:venom_state.
    (z.vs_requests,z.vs_call_ctx,z.vs_accounts,z.vs_transient,
     z.vs_allocas,z.vs_initial_fmp,z.vs_fmp)``) >> simp[]
QED

Theorem abi_decode_ptr_reentry_inst:
  abi_decoder_vars_extend extras s t /\ abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = OK u /\ ptr_inst_ok D lo fuel ctx fn G tn inst s ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst t
Proof
  strip_tac >> drule_all abi_decoder_step_inputs_defined >> strip_tac >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  drule_all abi_decode_ptr_reentry_access >> strip_tac >>
  drule_all abi_decode_ptr_reentry_taint_ok >> strip_tac >>
  drule_all abi_decoder_reentry_non_invoke >> strip_tac >>
  `step_inst fuel ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  rename1 `step_inst_base inst t = OK v` >>
  `step_inst fuel ctx inst t = OK v` by simp[step_inst_non_invoke] >>
  imp_res_tac abi_decode_ptr_reentry_check_frame >>
  gvs[ptr_inst_ok_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED
