Theory algebraicOptMainResidualStepProofs
Ancestors
  algebraicOptMainResidualProofs algebraicOptDefs opcodeClass list venomInst

Theorem ao_residual_opcode_partition:
  ~MEM opc
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE] /\
  ~MEM opc [PHI; INVOKE; JNZ; ASSERT; ASSERT_UNREACHABLE] ==>
  MEM opc [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP;
    ALLOCA; NOP; INVALID; RET; RETFMP; STOP; SINK; RETURN; REVERT;
    SELFDESTRUCT; DRET; RETURNDATACOPY; CREATE; CREATE2] \/
  MEM opc [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE;
    MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; CALLDATALOAD; EXTCODEHASH; ILOAD; DLOAD] \/
  MEM opc [MSTORE; MSTORE8; SSTORE; TSTORE; ISTORE] \/
  MEM opc [MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES] \/
  MEM opc [BYTE; OFFSET; ADDMOD; MULMOD] \/
  MEM opc [NOT; ASSIGN] \/
  MEM opc [SHA3; EXTCODECOPY; SETFMP; DALLOCA; BUMP; JMP; DJMP; LOG;
           CALL; STATICCALL; DELEGATECALL]
Proof
  Cases_on `opc` >> simp[MEM]
QED

Theorem ao_main_residual_ordinary_OK:
  inst_wf inst /\
  ~MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE] /\
  ~MEM inst.inst_opcode [PHI; INVOKE; JNZ; ASSERT; ASSERT_UNREACHABLE] /\
  ~MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP;
    ALLOCA; NOP; INVALID; RET; RETFMP; STOP; SINK; RETURN; REVERT;
    SELFDESTRUCT; DRET; RETURNDATACOPY; CREATE; CREATE2] /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (ao_resolve_iszero_op targets inst.inst_opcode a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  step_inst_base inst s = OK t ==>
  ?u. step_inst_base (ao_resolve_iszero_inst targets inst) r = OK u /\
    ao_main_observations fn V t u /\
    (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
    (if MEM inst.inst_opcode [JMP; DJMP] then
       t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0
     else t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx)
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE;
     MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; CALLDATALOAD; EXTCODEHASH; ILOAD; DLOAD]`
  >- suspend "reads" >>
  Cases_on `MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE; ISTORE]`
  >- suspend "stores" >>
  Cases_on `MEM inst.inst_opcode [MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES]`
  >- suspend "copies" >>
  Cases_on `MEM inst.inst_opcode [BYTE; OFFSET; ADDMOD; MULMOD]`
  >- suspend "pure" >>
  Cases_on `MEM inst.inst_opcode [NOT; ASSIGN]`
  >- suspend "unary" >>
  drule_all ao_residual_opcode_partition >> simp[MEM] >> strip_tac >> gvs[]
  >- suspend "sha3"
  >- suspend "extcodecopy"
  >- suspend "setfmp"
  >- suspend "dalloca"
  >- suspend "bump"
  >- suspend "jmp"
  >- suspend "djmp"
  >- suspend "log"
  >- suspend "call"
  >- suspend "staticcall" >> suspend "delegatecall"
QED

Resume ao_main_residual_ordinary_OK[reads]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  irule ao_main_read_resolved_OK >> simp[]
QED
Resume ao_main_residual_ordinary_OK[stores]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  irule ao_main_store_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets inst.inst_opcode`] >> fs[MEM]
QED
Resume ao_main_residual_ordinary_OK[copies]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  irule ao_main_copy3_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets inst.inst_opcode`] >> fs[MEM]
QED
Resume ao_main_residual_ordinary_OK[pure]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  irule ao_main_pure_residual_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets inst.inst_opcode`] >> fs[MEM]
QED
Resume ao_main_residual_ordinary_OK[unary]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  irule ao_main_unary_residual_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets inst.inst_opcode`] >> fs[MEM]
QED
Resume ao_main_residual_ordinary_OK[sha3]:
  simp[MEM] >> irule ao_main_sha3_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets SHA3`] >> simp[]
QED
Resume ao_main_residual_ordinary_OK[extcodecopy]:
  simp[MEM] >> irule ao_main_extcodecopy_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets EXTCODECOPY`] >> simp[]
QED
Resume ao_main_residual_ordinary_OK[setfmp]:
  simp[MEM] >> irule ao_main_setfmp_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets SETFMP`] >> simp[]
QED
Resume ao_main_residual_ordinary_OK[dalloca]:
  simp[MEM] >> irule ao_main_dalloca_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets DALLOCA`] >> simp[]
QED
Resume ao_main_residual_ordinary_OK[bump]:
  simp[MEM] >> irule ao_main_bump_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets BUMP`] >> simp[]
QED
Resume ao_main_residual_ordinary_OK[jmp]:
  simp[MEM] >> irule ao_main_jmp_base >> simp[] >> qexists_tac `s` >> simp[]
QED
Resume ao_main_residual_ordinary_OK[djmp]:
  simp[MEM] >> irule ao_main_djmp_base >> simp[] >> qexists_tac `s` >> simp[]
QED
Resume ao_main_residual_ordinary_OK[log]:
  `?tc ops. inst.inst_operands = Lit tc :: ops` by gvs[venomWfTheory.inst_wf_def] >>
  simp[MEM] >> irule ao_main_log_base >>
  simp[ao_resolve_iszero_inst_def, ao_resolve_iszero_op_def] >>
  qexistsl_tac [`inst`, `ops`, `ao_resolve_iszero_op targets LOG`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
Resume ao_main_residual_ordinary_OK[call]:
  simp[MEM] >> irule ao_main_call_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets CALL`] >> simp[MEM]
QED
Resume ao_main_residual_ordinary_OK[staticcall]:
  simp[MEM] >> irule ao_main_call_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets STATICCALL`] >> simp[MEM]
QED
Resume ao_main_residual_ordinary_OK[delegatecall]:
  simp[MEM] >> irule ao_main_delegatecall_base >> simp[ao_resolve_iszero_inst_def] >>
  qexistsl_tac [`inst`, `ao_resolve_iszero_op targets DELEGATECALL`] >> simp[]
QED
Finalise ao_main_residual_ordinary_OK

Theorem ao_main_residual_exact_base:
  inst_wf inst /\
  ~MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE] /\
  ~MEM inst.inst_opcode [PHI; INVOKE; JNZ; ASSERT; ASSERT_UNREACHABLE] /\
  (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
    eval_operand (ao_resolve_iszero_op targets inst.inst_opcode a) r = SOME w) /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  (?e. step_inst_base inst s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      (if MEM inst.inst_opcode [JMP; DJMP] then
         t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0
       else t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx))
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst_base inst s) (step_inst_base (ao_resolve_iszero_inst targets inst) r)
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP]`
  >- suspend "parameter" >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- suspend "alloca" >>
  Cases_on `MEM inst.inst_opcode [NOP; INVALID]`
  >- suspend "nop" >>
  Cases_on `MEM inst.inst_opcode [RET; RETFMP]`
  >- suspend "ret" >>
  Cases_on `MEM inst.inst_opcode [STOP; SINK]`
  >- suspend "stop" >>
  Cases_on `MEM inst.inst_opcode [RETURN; REVERT]`
  >- suspend "return" >>
  Cases_on `inst.inst_opcode = SELFDESTRUCT`
  >- suspend "selfdestruct" >>
  Cases_on `inst.inst_opcode = DRET`
  >- suspend "dret" >>
  Cases_on `inst.inst_opcode = RETURNDATACOPY`
  >- suspend "returndatacopy" >>
  Cases_on `MEM inst.inst_opcode [CREATE; CREATE2]`
  >- suspend "create" >>
  Cases_on `step_inst_base inst s` >> simp[]
  >- suspend "ordinary"
  >- (drule step_inst_base_halt_opcodes >> fs[MEM])
  >- (drule step_inst_base_abort_opcodes >> fs[MEM]) >>
  drule step_inst_base_intret_opcodes >> fs[MEM]
QED

Resume ao_main_residual_exact_base[parameter]:
  drule_all ao_main_parameter_base >>
  disch_then (qspec_then `targets` strip_assume_tac) >>
  fs[stateEquivTheory.lift_result_def, MEM]
QED
Resume ao_main_residual_exact_base[alloca]:
  drule_all ao_main_alloca_base >>
  disch_then (qspec_then `targets` strip_assume_tac) >>
  fs[stateEquivTheory.lift_result_def, MEM]
QED
Resume ao_main_residual_exact_base[nop]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  disj2_tac >> irule ao_main_nop_invalid_base >> simp[ao_resolve_iszero_inst_def]
QED
Resume ao_main_residual_exact_base[ret]:
  irule ao_main_ret_base >> simp[ao_resolve_iszero_inst_def] >>
  qexists_tac `ao_resolve_iszero_op targets inst.inst_opcode` >> simp[]
QED
Resume ao_main_residual_exact_base[stop]:
  disj2_tac >> irule ao_main_stop_base >> simp[ao_resolve_iszero_inst_def]
QED
Resume ao_main_residual_exact_base[return]:
  irule ao_main_return_revert_base >> simp[ao_resolve_iszero_inst_def] >>
  qexists_tac `ao_resolve_iszero_op targets inst.inst_opcode` >> simp[]
QED
Resume ao_main_residual_exact_base[selfdestruct]:
  irule ao_main_selfdestruct_base >> fs[ao_resolve_iszero_inst_def] >>
  qexists_tac `ao_resolve_iszero_op targets SELFDESTRUCT` >> simp[]
QED
Resume ao_main_residual_exact_base[dret]:
  irule ao_main_dret_resolved >> fs[]
QED
Resume ao_main_residual_exact_base[returndatacopy]:
  fs[] >> irule ao_main_returndatacopy_base >> simp[ao_resolve_iszero_inst_def] >>
  qexists_tac `ao_resolve_iszero_op targets RETURNDATACOPY` >> simp[]
QED
Resume ao_main_residual_exact_base[create]:
  `~MEM inst.inst_opcode [JMP; DJMP]` by fs[MEM] >> simp[] >>
  irule ao_main_create_base >> simp[ao_resolve_iszero_inst_def] >>
  qexists_tac `ao_resolve_iszero_op targets inst.inst_opcode` >> simp[]
QED
Resume ao_main_residual_exact_base[ordinary]:
  `~MEM inst.inst_opcode
    [PARAM; FMP_PARAM; RETPC_PARAM; GETFMP; INITIAL_FMP; ALLOCA;
     NOP; INVALID; RET; RETFMP; STOP; SINK; RETURN; REVERT;
     SELFDESTRUCT; DRET; RETURNDATACOPY; CREATE; CREATE2]` by fs[MEM] >>
  drule_all ao_main_residual_ordinary_OK >> strip_tac >>
  fs[stateEquivTheory.lift_result_def, MEM]
QED
Finalise ao_main_residual_exact_base
