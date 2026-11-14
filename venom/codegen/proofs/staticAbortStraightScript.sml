(* Value-independent, height-only progress for straight emitted opcodes. *)
Theory staticAbortStraight
Ancestors
  staticAbortTrace asmSymSem asmSem asmIR stackOpSim list arithmetic

Definition static_abort_straight_def:
  static_abort_straight name (outputs:num) <=>
    (outputs = 0 /\ MEM name
      ["POP"; "MSTORE"; "MSTORE8"; "MCOPY"; "CALLDATACOPY";
       "RETURNDATACOPY"; "CODECOPY"; "EXTCODECOPY"; "JUMPDEST"]) \/
    (outputs = 1 /\ MEM name
      ["ADD"; "MUL"; "SUB"; "DIV"; "SDIV"; "MOD"; "SMOD"; "EXP";
       "ADDMOD"; "MULMOD"; "LT"; "GT"; "SLT"; "SGT"; "EQ"; "ISZERO";
       "AND"; "OR"; "XOR"; "NOT"; "SHL"; "SHR"; "SAR"; "SIGNEXTEND";
       "BYTE"; "MLOAD"; "MSIZE"; "SLOAD"; "TLOAD"; "SHA3";
       "CALLER"; "ADDRESS"; "CALLVALUE"; "GAS"; "CALLDATASIZE";
       "CALLDATALOAD"; "ORIGIN"; "GASPRICE"; "CHAINID"; "COINBASE";
       "TIMESTAMP"; "NUMBER"; "PREVRANDAO"; "GASLIMIT"; "BASEFEE";
       "BLOBBASEFEE"; "BLOCKHASH"; "BLOBHASH"; "BALANCE"; "SELFBALANCE";
       "CODESIZE"; "EXTCODESIZE"; "EXTCODEHASH"; "RETURNDATASIZE"])
End

Theorem static_abort_straight_known:
  static_abort_straight name outputs ==>
  IS_SOME (evm_opcode_byte name) /\
  ~MEM name ["CALL"; "CALLCODE"; "STATICCALL"; "DELEGATECALL";
             "CREATE"; "CREATE2"; "SELFDESTRUCT"]
Proof
  simp[static_abort_straight_def] >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem static_abort_straight_dispatch:
  static_abort_straight name outputs /\
  asm_op_arity name <= LENGTH s.as_stack ==>
  (?t. asm_step lo o2pc (AsmOp name) s = AsmOK t /\
       t.as_pc = s.as_pc + 1 /\
       LENGTH t.as_stack = LENGTH s.as_stack - asm_op_arity name + outputs /\
       t.as_call_ctx = s.as_call_ctx /\ t.as_requests = s.as_requests) \/
  asm_step lo o2pc (AsmOp name) s = AsmFault (s with as_returndata := [])
Proof
  simp[static_abort_straight_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `_ <= LENGTH _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >> strip_tac >>
  simp[asm_step_def, asm_step_op_def] >>
  simp[asm_step_arith_def] >> simp[asm_step_compare_def] >>
  simp[asm_step_bitwise_def] >> simp[asm_step_memory_def] >>
  simp[asm_step_control_def] >> simp[asm_step_extcall_def] >>
  simp[asm_step_copy_def] >> simp[asm_step_context_def] >>
  fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] >>
  simp[asm_pop_def, asm_mstore_def, asm_mstore8_def, asm_mcopy_def,
       asm_copy_to_mem_def, asm_returndatacopy_def, asm_extcodecopy_def,
       asm_binop_def, asm_unop_def, asm_ternop_def, asm_mload_def,
       asm_sload_def, asm_tload_def, asm_sha3_def, asm_push_val_def,
       asm_gas_def, asm_state_unop_def, asm_next_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV asm_op_arity_def THENC EVAL)) >>
  simp[]
  >- (IF_CASES_TAC >> simp[]) >>
  Cases_on `s.as_gas_readings` >> simp[]
QED

Theorem static_abort_straight_step:
  static_abort_straight name outputs /\
  asm_op_arity name <= LENGTH s.as_stack /\
  asm_block_at prog s.as_pc [AsmOp name] ==>
  (?t. static_abort_normal lo o2pc prog 1 s t /\
       t.as_pc = s.as_pc + 1 /\
       LENGTH t.as_stack = LENGTH s.as_stack - asm_op_arity name + outputs /\
       t.as_call_ctx = s.as_call_ctx) \/
  (?t. static_abort_exception lo o2pc prog 1 s t)
Proof
  strip_tac >>
  `s.as_pc < LENGTH prog /\ EL s.as_pc prog = AsmOp name` by
    fs[asm_block_at_cons] >>
  `static_abort_safe_at prog s` by
    (drule static_abort_straight_known >>
     simp[static_abort_safe_at_def]) >>
  `static_abort_trace lo o2pc prog 1 s` by
    (simp[static_abort_trace_def, asm_steps_def]) >>
  drule_all static_abort_straight_dispatch >>
  disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac)
  >- (disj1_tac >> qexists `t` >>
      simp[static_abort_normal_def] >>
      rewrite_tac[numLib.num_CONV ``1:num``] >> simp[asm_steps_def]) >>
  disj2_tac >> qexists `s with as_returndata := []` >>
  simp[static_abort_exception_def] >>
  rewrite_tac[numLib.num_CONV ``1:num``] >> simp[asm_steps_def]
QED
