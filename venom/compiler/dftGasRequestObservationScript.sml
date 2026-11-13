(* Instruction-level request observations for directional DFT swaps. *)
Theory dftGasRequestObservation
Ancestors
  dftGasSimLocalBoundary dftGasOracleDefs venomExecSemantics venomState
  venomInst opcodeClass venomCallOracleDefs extCallOracle oracleExecProps list rich_list
Libs
  stepInstBaseLib

Theorem step_inst_base_abort_requests:
  step_inst_base i s = Abort a t ==> t.vs_requests = s.vs_requests
Proof
  strip_tac >> drule step_inst_base_abort_opcodes >> strip_tac >>
  with_opcode_clause gvs >>
  gvs[AllCaseEqs(), exec_create_abort_iff, halt_state_def,
      set_returndata_def, revert_state_def, exec_write2_def,
      exec_ext_call_def]
QED


Theorem step_inst_base_requests_prefix:
  step_inst_base i s = OK t ==> s.vs_requests <<= t.vs_requests
Proof
  Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[] >> strip_tac >> with_opcode_clause gvs >>
      gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
          AllCaseEqs(), update_var_def, record_request_def, IS_PREFIX_APPEND] >>
      metis_tac[]) >>
  strip_tac >> gvs[] >> drule_all step_inst_base_oracle >> simp[]
QED

(* Lift through the non-INVOKE execution wrapper without opening calls. *)
Theorem step_inst_abort_requests:
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = Abort a t ==>
  t.vs_requests = s.vs_requests
Proof
  strip_tac >> gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_abort_requests]
QED

Theorem step_inst_requests_prefix:
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t ==>
  s.vs_requests <<= t.vs_requests
Proof
  strip_tac >> gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_requests_prefix]
QED

(* GAS uses an event oracle but still changes only a variable. *)
Theorem ev_step_abort_requests:
  i.inst_opcode <> INVOKE /\ ev_step orc p d fuel C i s = Abort a t ==>
  t.vs_requests = s.vs_requests
Proof
  Cases_on `i.inst_opcode = GAS`
  >- simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  strip_tac >> gvs[ev_step_ordinary] >> metis_tac[step_inst_abort_requests]
QED

Theorem ev_step_requests_prefix:
  i.inst_opcode <> INVOKE /\ ev_step orc p d fuel C i s = OK t ==>
  s.vs_requests <<= t.vs_requests
Proof
  Cases_on `i.inst_opcode = GAS`
  >- (simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[update_var_def]) >>
  strip_tac >> gvs[ev_step_ordinary] >> metis_tac[step_inst_requests_prefix]
QED

Theorem ev_step_request_free:
  ~MEM i.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  ev_step orc p d fuel C i s = OK t ==> t.vs_requests = s.vs_requests
Proof
  Cases_on `i.inst_opcode = GAS`
  >- (simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[update_var_def]) >>
  strip_tac >> gvs[ev_step_ordinary] >>
  drule_all step_inst_noninvoke_oracle >> simp[]
QED
