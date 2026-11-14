Theory readonlyInvokeCopyFwdExecutionBuiltins
Ancestors
  readonlyInvokeCopyFwdExecutionPointNext readonlyInvokeCopyFwdExecutionPointLocal
  readonlyInvokeCopyFwdExecutionPointScalars readonlyInvokeCopyFwdExecutionPointLoads
  readonlyInvokeCopyFwdExecutionPointStores readonlyInvokeCopyFwdExecutionPointData
  readonlyInvokeCopyFwdExecutionPointObservers readonlyInvokeCopyFwdExecutionWordLoads
  readonlyInvokeCopyFwdExecutionSteps o1PassContract unitShapeDefs contextCodegenRel
  venomExecSemantics venomWf venomInst venomState ptrDiscipline
  finite_map list words

Theorem ricf_execution_point_builtin:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
    SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD;ADD;SUB;LT;GT;EQ;SHL;SHR;SAR;SIGNEXTEND;BYTE;GAS;
    CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;TIMESTAMP;NUMBER;
    PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;CALLDATASIZE;RETURNDATASIZE;CODESIZE;
    SELFBALANCE;BLOCKHASH;BLOBHASH;BALANCE;EXTCODESIZE;EXTCODEHASH;CALLDATALOAD;DLOAD;
    SLOAD;TLOAD;MLOAD;ILOAD;MSTORE;ISTORE;MSTORE8;SSTORE;TSTORE;ASSERT;ASSERT_UNREACHABLE;CALLDATACOPY;DLOADBYTES;CODECOPY;RETURNDATACOPY;EXTCODECOPY;SHA3;LOG;BUMP;ALLOCA;PARAM;RETPC_PARAM;ASSIGN;NOP;INITIAL_FMP] /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn /\ opaque_use_ok fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_ssa_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  Cases_on `MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
    SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD]`
  >- (drule_all ricf_execution_point_scalar >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [ADD;SUB;LT;GT;EQ;SHL;SHR;SAR;SIGNEXTEND;BYTE;GAS;
    CALLER;ADDRESS;CALLVALUE;ORIGIN;GASPRICE;CHAINID;COINBASE;TIMESTAMP;NUMBER;
    PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;CALLDATASIZE;RETURNDATASIZE;CODESIZE;
    SELFBALANCE;BLOCKHASH;BLOBHASH;BALANCE;EXTCODESIZE;EXTCODEHASH;CALLDATALOAD;DLOAD]`
  >- (drule_all ricf_execution_point_scalar_remaining >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [SLOAD;TLOAD]`
  >- (irule ricf_execution_point_ordinary >> simp[] >>
      `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
       inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
       inst.inst_opcode <> MCOPY` by fs[MEM, is_terminator_def] >>
      simp[] >> rpt gen_tac >> strip_tac >>
      drule_all ricf_execution_storage_load_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [MLOAD;ILOAD]`
  >- (`?addr. inst.inst_operands = [addr]` by
        (qpat_assum `inst_wf inst` mp_tac >>
         qpat_assum `MEM inst.inst_opcode [MLOAD;ILOAD]` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[MEM, inst_wf_def, LENGTH_EQ_NUM_compute]) >>
      drule_all ricf_execution_point_wordload >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [MSTORE;ISTORE]`
  >- (drule_all ricf_execution_point_word_store >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = MSTORE8`
  >- (drule_all ricf_execution_point_byte_store >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [SSTORE;TSTORE]`
  >- (drule_all ricf_execution_point_storage_store >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE]`
  >- (drule_all ricf_execution_point_assert >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [CALLDATACOPY;DLOADBYTES;CODECOPY]`
  >- (drule_all ricf_execution_point_data_write >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [RETURNDATACOPY]`
  >- (drule_all ricf_execution_point_return_data >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [EXTCODECOPY]`
  >- (drule_all ricf_execution_point_external_data >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = SHA3`
  >- (drule_all ricf_execution_point_sha3 >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = LOG`
  >- (drule_all ricf_execution_point_log >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (drule_all ricf_execution_point_bump >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (`?amount out. inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out]` by
        gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      drule_all ricf_execution_point_alloca >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [PARAM;RETPC_PARAM]`
  >- (`?idx out. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out]` by
        (qpat_assum `inst_wf inst` mp_tac >>
         qpat_assum `MEM inst.inst_opcode [PARAM;RETPC_PARAM]` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[MEM, inst_wf_def, LENGTH_EQ_NUM_compute]) >>
      drule_all ricf_execution_point_param >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (`?op out. inst.inst_operands = [op] /\ inst.inst_outputs = [out]` by
        gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      drule_all ricf_execution_point_assign >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (`inst.inst_outputs = []` by gvs[inst_wf_def] >>
      drule_all ricf_execution_point_nop >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `inst.inst_opcode = INITIAL_FMP` by fs[MEM] >>
  drule_all ricf_execution_point_initial_fmp >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED
