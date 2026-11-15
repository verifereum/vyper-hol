Theory readonlyInvokeCopyFwdExecutionPointScalars
Ancestors
  readonlyInvokeCopyFwdExecutionPointNext readonlyInvokeCopyFwdExecutionSteps
  readonlyInvokeCopyFwdExecutionArithmetic readonlyInvokeCopyFwdExecutionCompare
  readonlyInvokeCopyFwdExecutionShift readonlyInvokeCopyFwdExecutionScalarExtras
  readonlyInvokeCopyFwdExecutionReads readonlyInvokeCopyFwdExecutionGas
  readonlyInvokeCopyFwdExecution
  ptrDiscipline contextCodegenRel venomExecSemantics venomInst venomState
  list finite_map

Theorem ricf_execution_point_scalar_remaining:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  ssa_form fn /\ opaque_use_ok fn /\ ptr_discipline lo C vs /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [ADD;SUB;LT;GT;EQ;SHL;SHR;SAR;SIGNEXTEND;BYTE;GAS;
    CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;TIMESTAMP;NUMBER;
    PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;CALLDATASIZE;RETURNDATASIZE;CODESIZE;
    SELFBALANCE;BLOCKHASH;BLOBHASH;BALANCE;EXTCODESIZE;EXTCODEHASH;CALLDATALOAD;DLOAD] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
   inst.inst_opcode <> MCOPY` by fs[MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM inst.inst_opcode [ADD;SUB]`
  >- (drule_all ricf_execution_arithmetic_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [LT;GT;EQ]`
  >- (drule_all ricf_execution_comparison_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [SHL;SHR;SAR]`
  >- (drule_all ricf_execution_shift_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [SIGNEXTEND;BYTE;OFFSET]`
  >- (drule_all ricf_execution_byte_offset_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (drule_all ricf_execution_gas_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode
    [BLOCKHASH;BLOBHASH;BALANCE;EXTCODESIZE;EXTCODEHASH;CALLDATALOAD;DLOAD]`
  >- (drule_all ricf_execution_read1_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `MEM inst.inst_opcode [CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;
    COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
    CALLDATASIZE;RETURNDATASIZE;CODESIZE;RETPC_PARAM;GETFMP;INITIAL_FMP;SELFBALANCE]` by
    fs[MEM] >>
  drule_all ricf_execution_read0_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_assign:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\ ssa_form fn /\
  active_inst fn inst s /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ricf_execution_point_ordinary >>
  simp[is_terminator_def] >> rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_assign_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_initial_fmp:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  ssa_form fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = INITIAL_FMP /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ricf_execution_point_ordinary >>
  simp[is_terminator_def] >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`Ct` |-> `Ct`, `rt` |-> `tn`, `ledger` |-> `certificates`]
    ricf_execution_read0_next) >>
  (impl_tac >- simp[]) >> simp[]
QED
