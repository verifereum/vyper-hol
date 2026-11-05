Theory bodyIntCallStorageFrame
Ancestors
  exprLoweringProps venomExecSemantics venomState venomCallOracleDefs extCallOracle list

(* Explicit storage-readonly whitelist. Memory, variables and control flow
   may change; storage-changing calls and INVOKE are deliberately absent. *)
Definition readonly_opcode_def:
  readonly_opcode op <=> MEM op
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; MLOAD; MSTORE; MSTORE8; MCOPY; MEMTOP;
     SLOAD; TLOAD; ILOAD; ISTORE; JMP; JNZ; DJMP; PHI; PARAM; ASSIGN; NOP;
     ALLOCA; DALLOCA; GETFMP; SETFMP; INITIAL_FMP; BUMP;
     FMP_PARAM; RETPC_PARAM; CALLER; CALLVALUE; CALLDATALOAD;
     CALLDATASIZE; CALLDATACOPY; ADDRESS; ORIGIN; GASPRICE; GAS; GASLIMIT;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID; SELFBALANCE;
     BALANCE; BLOCKHASH; BASEFEE; CODESIZE; CODECOPY; EXTCODESIZE;
     EXTCODEHASH; EXTCODECOPY; RETURNDATASIZE; RETURNDATACOPY;
     BLOBHASH; BLOBBASEFEE; SHA3; STATICCALL; ASSERT; ASSERT_UNREACHABLE;
     DLOAD; DLOADBYTES; OFFSET]
End

Theorem consume_static_outcome_storage:
  rq.cr_static ==>
  contract_storage (SND (consume_call_outcome rq ro rs s)) = contract_storage s /\
  contract_transient (SND (consume_call_outcome rq ro rs s)) = contract_transient s
Proof
  strip_tac >> simp[contract_storage_def, contract_transient_def]
QED

Theorem exec_static_call_storage:
  exec_ext_call inst s gas addr value ao az ro rz T = OK t ==>
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s
Proof
  simp[exec_ext_call_def, venom_call_request_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, contract_storage_def, contract_transient_def]
QED

Theorem step_staticcall_storage:
  inst.inst_opcode = STATICCALL /\ step_inst_base inst s = OK t ==>
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  asm_rewrite_tac[step_inst_base_def] >>
  simp_tac (srw_ss()) [] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule exec_static_call_storage >> simp[]
QED

Theorem step_readonly_storage:
  readonly_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = STATICCALL`
  >- (drule_all step_staticcall_storage >> simp[]) >>
  Cases_on `inst.inst_opcode` >> gvs[readonly_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  asm_rewrite_tac[step_inst_base_def] >>
  simp_tac (srw_ss()) [] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def, exec_alloca_def,
      exec_gas_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[update_var_def, jump_to_def, mstore_def, mstore8_def, mcopy_def,
       istore_def, write_memory_with_expansion_def,
       contract_storage_def, contract_transient_def]
QED

Theorem run_readonly_storage:
  EVERY (\i. readonly_opcode i.inst_opcode) is /\
  run_inst_seq is s = OK t ==>
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s
Proof
  strip_tac >> fs[EVERY_MEM] >> conj_tac >>
  irule run_inst_seq_preserves_field >> qexists `is` >>
  simp[] >> rpt strip_tac >>
  `readonly_opcode i.inst_opcode` by (first_x_assum irule >> simp[]) >>
  drule_all step_readonly_storage >> simp[]
QED
