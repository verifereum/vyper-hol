Theory loadElimPaddedNoncall
Ancestors
  loadElimMemoryRel loadElimPaddedSimHelpers venomExecSemantics venomState
  stateFrame stateEquiv list finite_map venomMemProps venomCallOracleDefs

Definition le_padded_control_def:
  le_padded_control V s t <=>
    padded_exec_equiv V s t /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_inst_idx = t.vs_inst_idx /\ s.vs_prev_bb = t.vs_prev_bb
End

Theorem le_padded_operand_agreement:
  padded_exec_equiv V s t /\
  (!v. op = Var v ==> lookup_var v s = lookup_var v t) ==>
  eval_operand op s = eval_operand op t
Proof
  Cases_on `op` >> simp[eval_operand_def] >> strip_tac >>
  gvs[padded_exec_equiv_def, execution_frame_def, venom_state_component_equality]
QED

Theorem le_padded_operands_agreement:
  !ops. padded_exec_equiv V s t /\
  (!v. MEM (Var v) ops ==> lookup_var v s = lookup_var v t) ==>
  eval_operands ops s = eval_operands ops t
Proof
  Induct >- simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by
    (irule le_padded_operand_agreement >> metis_tac[MEM]) >>
  `eval_operands ops s = eval_operands ops t` by metis_tac[MEM] >>
  simp[eval_operands_def]
QED

Theorem le_padded_control_update_var:
  le_padded_control V s t ==>
  le_padded_control V (update_var v w s) (update_var v w t)
Proof
  simp[le_padded_control_def, padded_exec_equiv_update_var] >>
  simp[update_var_def]
QED

Theorem le_padded_exec_pure1:
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_pure1 f i s) (exec_pure1 f i t)
Proof
  strip_tac >> simp[exec_pure1_def] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "op2 tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_exec_pure2:
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_pure2 f i s) (exec_pure2 f i t)
Proof
  strip_tac >> simp[exec_pure2_def] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "op2 rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "op3 tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t /\
   eval_operand op2 s = eval_operand op2 t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op2 t` >> gvs[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_exec_pure3:
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_pure3 f i s) (exec_pure3 f i t)
Proof
  strip_tac >> simp[exec_pure3_def] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "op2 rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "op3 rest3"] >> simp[lift_result_def] >>
  namedCases_on `rest3` ["", "op4 tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t /\
   eval_operand op2 s = eval_operand op2 t /\
   eval_operand op3 s = eval_operand op3 t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op2 t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op3 t` >> gvs[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_exec_read0:
  le_padded_control V s t /\ f s = f t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_read0 f i s) (exec_read0 f i t)
Proof
  strip_tac >> simp[exec_read0_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_exec_read1:
  le_padded_control V s t /\ (!v. f v s = f v t) /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_read1 f i s) (exec_read1 f i t)
Proof
  strip_tac >> simp[exec_read1_def] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "op2 tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_exec_write2:
  le_padded_control V s t /\
  (!v w. le_padded_control V (f v w s) (f v w t)) /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_write2 f i s) (exec_write2 f i t)
Proof
  strip_tac >> simp[exec_write2_def] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "op2 rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "op3 tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t /\
   eval_operand op2 s = eval_operand op2 t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op2 t` >> gvs[lift_result_def]
QED

Theorem le_padded_arithmetic:
  MEM i.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
     SHL; SHR; SAR; SIGNEXTEND; BYTE; OFFSET] /\
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  Cases_on `i.inst_opcode` >> simp[] >> strip_tac >>
  simp[step_inst_base_opcode_eqs] >>
  metis_tac[le_padded_exec_pure1, le_padded_exec_pure2, le_padded_exec_pure3]
QED

Theorem le_padded_control_write_memory:
  le_padded_control V s t ==>
  le_padded_control V (write_memory_with_expansion off bytes s)
    (write_memory_with_expansion off bytes t)
Proof
  simp[le_padded_control_def, padded_exec_equiv_write_memory] >>
  simp[write_memory_with_expansion_def]
QED

Theorem le_padded_control_mstore:
  le_padded_control V s t ==>
  le_padded_control V (mstore off w s) (mstore off w t)
Proof
  simp[mstore_eq_write_mem, le_padded_control_write_memory]
QED

Theorem le_padded_control_mstore8:
  le_padded_control V s t ==>
  le_padded_control V (mstore8 off w s) (mstore8 off w t)
Proof
  simp[mstore8_eq_write_mem, le_padded_control_write_memory]
QED

Theorem le_padded_control_mcopy:
  le_padded_control V s t ==>
  le_padded_control V (mcopy dst src sz s) (mcopy dst src sz t)
Proof
  strip_tac >>
  `read_memory src sz s = read_memory src sz t` by
    metis_tac[le_padded_control_def, padded_exec_equiv_read_memory] >>
  gvs[read_memory_def] >>
  simp[mcopy_def, le_padded_control_write_memory]
QED

Theorem le_padded_operands_eq:
  !ops. (!op. MEM op ops ==> eval_operand op s = eval_operand op t) ==>
  eval_operands ops s = eval_operands ops t
Proof
  Induct >- simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by simp[] >>
  `eval_operands ops s = eval_operands ops t` by metis_tac[MEM] >>
  simp[eval_operands_def]
QED

Theorem le_padded_exec_gas:
  le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_gas i s) (exec_gas i t)
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  simp[exec_gas_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  Cases_on `t.vs_gas_readings` >> simp[lift_result_def, le_padded_control_update_var] >>
  irule le_padded_control_update_var >>
  gvs[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
      read_memory_def, execution_frame_def, venom_state_component_equality]
QED

Theorem le_padded_context_reads:
  MEM i.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     BLOCKHASH; BLOBHASH; BALANCE; SELFBALANCE; CALLDATASIZE; CALLDATALOAD;
     RETURNDATASIZE; CODESIZE; EXTCODESIZE; EXTCODEHASH; DLOAD;
     MLOAD; ILOAD; SLOAD; TLOAD] /\
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  Cases_on `i.inst_opcode` >> simp[] >> strip_tac >>
  simp[step_inst_base_opcode_eqs] >>
  FIRST [irule le_padded_exec_gas, irule le_padded_exec_read0, irule le_padded_exec_read1] >>
  simp[] >>
  `padded_exec_equiv V s t` by gvs[le_padded_control_def] >>
  drule padded_exec_equiv_mload >> strip_tac >>
  gvs[padded_exec_equiv_def, execution_frame_def,
      venom_state_component_equality, sload_def, tload_def,
      contract_storage_def, contract_transient_def, le_padded_control_def]
QED

Theorem le_padded_control_sstore:
  le_padded_control V s t ==>
  le_padded_control V (sstore key w s) (sstore key w t)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, sstore_def,
       lookup_var_def, read_memory_def, execution_frame_def,
       venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_control_tstore:
  le_padded_control V s t ==>
  le_padded_control V (tstore key w s) (tstore key w t)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, tstore_def,
       lookup_var_def, read_memory_def, execution_frame_def,
       venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_terminal_updates:
  padded_exec_equiv V s t ==>
  padded_exec_equiv V (halt_state s) (halt_state t) /\
  padded_exec_equiv V (revert_state s) (revert_state t) /\
  padded_exec_equiv V (set_returndata rd s) (set_returndata rd t)
Proof
  simp[padded_exec_equiv_def, halt_state_def, revert_state_def,
       set_returndata_def, lookup_var_def, read_memory_def,
       execution_frame_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_store_ops:
  MEM i.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE] /\
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  `padded_exec_equiv V s t` by gvs[le_padded_control_def] >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule le_padded_operands_eq >> simp[]) >>
  Cases_on `i.inst_opcode` >> gvs[] >>
  simp[step_inst_base_opcode_eqs] >>
  TRY (IF_CASES_TAC >- simp[lift_result_def, le_padded_terminal_updates]) >>
  simp[] >> irule le_padded_exec_write2 >>
  simp[le_padded_control_mstore, le_padded_control_mstore8,
       le_padded_control_sstore, le_padded_control_tstore]
QED

Theorem le_padded_mcopy_op:
  i.inst_opcode = MCOPY /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "dst rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "src rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "sz rest3"] >> simp[lift_result_def] >>
  namedCases_on `rest3` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand dst s = eval_operand dst t /\
   eval_operand src s = eval_operand src t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand dst t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand src t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >> gvs[lift_result_def, le_padded_control_mcopy]
QED

Theorem le_padded_control_istore:
  le_padded_control V s t ==>
  le_padded_control V (istore off w s) (istore off w t)
Proof
  strip_tac >>
  `le_padded_control V (mstore off w s) (mstore off w t)` by
    simp[le_padded_control_mstore] >>
  gvs[le_padded_control_def, padded_exec_equiv_def, istore_def,
      execution_frame_def, venom_state_component_equality,
      lookup_var_def, read_memory_def, mstore_def]
QED

Theorem le_padded_istore_op:
  i.inst_opcode = ISTORE /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "off rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "w rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand off s = eval_operand off t /\
   eval_operand w s = eval_operand w t` by simp[] >>
  Cases_on `eval_operand off t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand w t` >> gvs[lift_result_def, le_padded_control_istore]
QED

Theorem le_padded_return_revert:
  MEM i.inst_opcode [RETURN; REVERT] /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `padded_exec_equiv V s t` by gvs[le_padded_control_def] >>
  `!off sz. TAKE sz (DROP off s.vs_memory ++ REPLICATE sz 0w) =
            TAKE sz (DROP off t.vs_memory ++ REPLICATE sz 0w)` by
    metis_tac[padded_exec_equiv_read_memory, read_memory_def] >>
  Cases_on `i.inst_opcode` >> gvs[] >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "off rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "sz rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand off s = eval_operand off t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand off t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >> gvs[lift_result_def] >>
  metis_tac[le_padded_terminal_updates]
QED

Theorem le_padded_sha3:
  i.inst_opcode = SHA3 /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `padded_exec_equiv V s t` by gvs[le_padded_control_def] >>
  `!off sz. TAKE sz (DROP off s.vs_memory ++ REPLICATE sz 0w) =
            TAKE sz (DROP off t.vs_memory ++ REPLICATE sz 0w)` by
    metis_tac[padded_exec_equiv_read_memory, read_memory_def] >>
  simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "off rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "sz rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand off s = eval_operand off t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand off t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >> gvs[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_simple_terminal:
  MEM i.inst_opcode [STOP; SINK; NOP; PHI] /\ le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  Cases_on `i.inst_opcode` >> simp[] >> strip_tac >>
  simp[step_inst_base_opcode_eqs, lift_result_def] >>
  metis_tac[le_padded_control_def, le_padded_terminal_updates, set_returndata_def]
QED

Theorem le_padded_assertions:
  MEM i.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> Cases_on `i.inst_opcode` >> gvs[] >>
  simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "cond rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand cond s = eval_operand cond t` by simp[] >>
  Cases_on `eval_operand cond t` >> gvs[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def] >>
  metis_tac[le_padded_control_def, le_padded_terminal_updates]
QED

Theorem le_padded_control_jump:
  le_padded_control V s t ==>
  le_padded_control V (jump_to lbl s) (jump_to lbl t)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, jump_to_def,
       lookup_var_def, read_memory_def, execution_frame_def,
       venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

Theorem le_padded_jmp:
  i.inst_opcode = JMP /\ le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >> simp[lift_result_def] >>
  Cases_on `op` >> simp[lift_result_def, le_padded_control_jump]
QED

Theorem le_padded_djmp:
  i.inst_opcode = DJMP /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  Cases_on `extract_labels rest` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def, le_padded_control_jump]
QED

Theorem le_padded_jnz:
  i.inst_opcode = JNZ /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "nz rest2"] >> simp[lift_result_def] >>
  Cases_on `nz` >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "z rest3"] >> simp[lift_result_def] >>
  Cases_on `z` >> simp[lift_result_def] >>
  namedCases_on `rest3` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def, le_padded_control_jump]
QED

Theorem le_padded_internal_return:
  MEM i.inst_opcode [RET; RETFMP] /\ le_padded_control V s t /\
  eval_operands i.inst_operands s = eval_operands i.inst_operands t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_fmp = t.vs_fmp` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  Cases_on `i.inst_opcode` >> gvs[] >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `eval_operands i.inst_operands t` ["", "vals"] >>
  gvs[lift_result_def] >> Cases_on `vals` >>
  simp[lift_result_def] >> gvs[le_padded_control_def]
QED

Theorem le_padded_assign:
  i.inst_opcode = ASSIGN /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >> simp[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_context_copy:
  MEM i.inst_opcode [CALLDATACOPY; DLOADBYTES; CODECOPY; RETURNDATACOPY] /\
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
   s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  Cases_on `i.inst_opcode` >> gvs[] >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "dst rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "src rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "sz rest3"] >> simp[lift_result_def] >>
  namedCases_on `rest3` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand dst s = eval_operand dst t /\
   eval_operand src s = eval_operand src t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand dst t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand src t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >> gvs[lift_result_def] >>
  simp[le_padded_control_write_memory] >>
  IF_CASES_TAC >> simp[lift_result_def, le_padded_control_write_memory] >>
  metis_tac[le_padded_control_def, le_padded_terminal_updates]
QED

Theorem le_padded_extcodecopy:
  i.inst_opcode = EXTCODECOPY /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "addr rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "dst rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "src rest3"] >> simp[lift_result_def] >>
  namedCases_on `rest3` ["", "sz rest4"] >> simp[lift_result_def] >>
  namedCases_on `rest4` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand addr s = eval_operand addr t /\
   eval_operand dst s = eval_operand dst t /\
   eval_operand src s = eval_operand src t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand addr t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand dst t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand src t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >>
  gvs[lift_result_def, le_padded_control_write_memory]
QED

Theorem le_padded_control_fmp:
  le_padded_control V s t ==>
  le_padded_control V (s with vs_fmp := w) (t with vs_fmp := w)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_fmp_reads:
  MEM i.inst_opcode [GETFMP; INITIAL_FMP] /\ le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_fmp = t.vs_fmp /\ s.vs_initial_fmp = t.vs_initial_fmp` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  Cases_on `i.inst_opcode` >> gvs[] >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_fmp_write:
  MEM i.inst_opcode [SETFMP; DALLOCA] /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_fmp = t.vs_fmp` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  Cases_on `i.inst_opcode` >> gvs[] >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >>
  simp[lift_result_def, le_padded_control_fmp] >>
  Cases_on `outs` >>
  simp[lift_result_def, le_padded_control_fmp, le_padded_control_update_var]
QED

Theorem le_padded_params:
  MEM i.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM] /\ le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_params = t.vs_params /\ s.vs_return_pc_token = t.vs_return_pc_token` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  Cases_on `i.inst_opcode` >> gvs[] >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  Cases_on `op` >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >> simp[lift_result_def] >>
  Cases_on `w2n c < LENGTH t.vs_params` >> simp[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_bump:
  i.inst_opcode = BUMP /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "base_op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "sz rest2"] >> simp[lift_result_def] >>
  namedCases_on `rest2` ["", "extra tail"] >> simp[lift_result_def] >>
  namedCases_on `i.inst_outputs` ["", "ptr outs"] >> simp[lift_result_def] >>
  namedCases_on `outs` ["", "next outs2"] >> simp[lift_result_def] >>
  namedCases_on `outs2` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand base_op s = eval_operand base_op t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand base_op t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >>
  gvs[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_control_allocas:
  le_padded_control V s t ==>
  le_padded_control V
    (s with <|vs_allocas := a; vs_alloca_next := n|>)
    (t with <|vs_allocas := a; vs_alloca_next := n|>)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_exec_alloca:
  le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_alloca i s sz) (exec_alloca i t sz)
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  simp[exec_alloca_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  Cases_on `FLOOKUP t.vs_allocas i.inst_id` >>
  simp[lift_result_def, le_padded_control_update_var, le_padded_control_allocas] >>
  Cases_on `x` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_alloca:
  i.inst_opcode = ALLOCA /\ le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  Cases_on `op` >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >>
  simp[lift_result_def, le_padded_exec_alloca]
QED

Theorem le_padded_control_accounts:
  le_padded_control V s t ==>
  le_padded_control V
    (s with <|vs_accounts := a; vs_pending_deletions := d|>)
    (t with <|vs_accounts := a; vs_pending_deletions := d|>)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_selfdestruct:
  i.inst_opcode = SELFDESTRUCT /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_call_ctx = t.vs_call_ctx /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule le_padded_operands_eq >> simp[]) >>
  simp[step_inst_base_opcode_eqs] >>
  IF_CASES_TAC >-
    (simp[lift_result_def] >> metis_tac[le_padded_terminal_updates, le_padded_control_def]) >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "extra tail"] >> simp[lift_result_def] >>
  `eval_operand op s = eval_operand op t` by simp[] >>
  Cases_on `eval_operand op t` >> gvs[lift_result_def] >>
  metis_tac[le_padded_terminal_updates, le_padded_control_accounts,
            le_padded_control_def]
QED

Theorem le_padded_invalid:
  i.inst_opcode = INVALID /\ le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, lift_result_def] >>
  metis_tac[le_padded_terminal_updates, le_padded_control_def]
QED

Theorem le_padded_pack_dynamic:
  !pairs cursor s t ps cs s' pt ct t'.
  le_padded_control V s t /\
  pack_dret_dynamic cursor pairs s = (ps,cs,s') /\
  pack_dret_dynamic cursor pairs t = (pt,ct,t') ==>
  ps = pt /\ cs = ct /\ le_padded_control V s' t'
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  first_x_assum irule >>
  metis_tac[le_padded_control_mcopy]
QED

Theorem le_padded_dret:
  i.inst_opcode = DRET /\ le_padded_control V s t /\
  eval_operands i.inst_operands s = eval_operands i.inst_operands t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_entry_fmp = t.vs_call_entry_fmp` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  simp[step_inst_base_opcode_eqs] >>
  Cases_on `i.inst_outputs = []` >> simp[lift_result_def] >>
  namedCases_on `parse_dret_shape i` ["", "shape"] >> simp[lift_result_def] >>
  PairCases_on `shape` >> simp[] >>
  namedCases_on `eval_operands i.inst_operands t` ["", "vals"] >>
  gvs[lift_result_def] >>
  namedCases_on `pair_dret_words (TAKE (2 * shape1) (DROP (shape0 + 1) vals))`
    ["", "pairs"] >> simp[lift_result_def] >>
  rpt (pairarg_tac >> simp[]) >>
  drule_all le_padded_pack_dynamic >> strip_tac >> gvs[lift_result_def] >>
  metis_tac[le_padded_control_fmp, le_padded_control_def]
QED

Theorem le_padded_control_logs:
  le_padded_control V s t ==>
  le_padded_control V (s with vs_logs := logs) (t with vs_logs := logs)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_log:
  i.inst_opcode = LOG /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  (!ops. EVERY (\op. MEM op i.inst_operands) ops ==>
         eval_operands ops s = eval_operands ops t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_logs = t.vs_logs` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule le_padded_operands_eq >> simp[]) >>
  simp[step_inst_base_opcode_eqs] >>
  IF_CASES_TAC >-
    (simp[lift_result_def] >> metis_tac[le_padded_terminal_updates, le_padded_control_def]) >>
  namedCases_on `i.inst_operands` ["", "op rest"] >> simp[lift_result_def] >>
  Cases_on `op` >> simp[lift_result_def] >>
  Cases_on `LENGTH rest = w2n c + 2` >> simp[lift_result_def] >>
  `MEM (EL 0 (REVERSE rest)) rest /\ MEM (EL 1 (REVERSE rest)) rest` by
    (conj_tac >> once_rewrite_tac[GSYM MEM_REVERSE] >>
     irule EL_MEM >> simp[]) >>
  `EVERY (\op. MEM op i.inst_operands) (DROP 2 (REVERSE rest))` by
    (simp[EVERY_MEM] >> rpt strip_tac >> disj2_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  `eval_operand (EL 0 (REVERSE rest)) s = eval_operand (EL 0 (REVERSE rest)) t /\
   eval_operand (EL 1 (REVERSE rest)) s = eval_operand (EL 1 (REVERSE rest)) t /\
   eval_operands (DROP 2 (REVERSE rest)) s = eval_operands (DROP 2 (REVERSE rest)) t`
    by metis_tac[MEM] >>
  Cases_on `eval_operand (EL 0 (REVERSE rest)) t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand (EL 1 (REVERSE rest)) t` >> gvs[lift_result_def] >>
  Cases_on `eval_operands (DROP 2 (REVERSE rest)) t` >> gvs[lift_result_def] >>
  `!off sz. read_memory off sz s = read_memory off sz t` by
    metis_tac[padded_exec_equiv_read_memory, le_padded_control_def] >>
  gvs[read_memory_def] >> simp[le_padded_control_logs]
QED

Theorem le_padded_requests:
  le_padded_control V s t ==>
  venom_call_request s addr value off sz static =
    venom_call_request t addr value off sz static /\
  venom_create_request s value off sz salt =
    venom_create_request t value off sz salt
Proof
  strip_tac >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t` by
    metis_tac[le_padded_control_def, padded_exec_equiv_read_memory] >>
  gvs[venom_call_request_def, venom_create_request_def, le_padded_control_def,
      padded_exec_equiv_def, execution_frame_def, venom_state_component_equality]
QED

Theorem le_padded_consume_call:
  le_padded_control V s t ==>
  FST (consume_call_outcome rq ro rs s) = FST (consume_call_outcome rq ro rs t) /\
  le_padded_control V (SND (consume_call_outcome rq ro rs s))
    (SND (consume_call_outcome rq ro rs t))
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests /\
   s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
   s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  `!bytes. le_padded_control V (write_memory_with_expansion ro bytes s)
      (write_memory_with_expansion ro bytes t)` by
    simp[le_padded_control_write_memory] >>
  simp[consume_call_outcome_eq] >>
  gvs[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
      read_memory_def, execution_frame_def, venom_state_component_equality,
      write_memory_with_expansion_def]
QED

Theorem le_padded_exec_ext_call:
  le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_ext_call i s gas addr value ao az ro rz static)
    (exec_ext_call i t gas addr value ao az ro rz static)
Proof
  strip_tac >>
  `venom_call_request s addr value ao az static =
   venom_call_request t addr value ao az static` by
    metis_tac[le_padded_requests] >>
  simp[exec_ext_call_def] >> rpt (pairarg_tac >> simp[]) >>
  drule le_padded_consume_call >>
  disch_then (qspecl_then [`w2n rz`,
                         `venom_call_request t addr value ao az static`, `w2n ro`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_consume_create:
  le_padded_control V s t ==>
  FST (consume_create_outcome rq s) = FST (consume_create_outcome rq t) /\
  le_padded_control V (SND (consume_create_outcome rq s))
    (SND (consume_create_outcome rq t))
Proof
  simp[consume_create_outcome_eq, le_padded_control_def, padded_exec_equiv_def,
       lookup_var_def, read_memory_def, execution_frame_def,
       venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

Theorem le_padded_exec_create:
  le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_create i s value off sz salt) (exec_create i t value off sz salt)
Proof
  strip_tac >>
  `venom_create_request s value off sz salt =
   venom_create_request t value off sz salt` by metis_tac[le_padded_requests] >>
  simp[exec_create_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  IF_CASES_TAC >-
    metis_tac[le_padded_terminal_updates, le_padded_control_def, lift_result_def] >>
  rpt (pairarg_tac >> simp[]) >>
  drule le_padded_consume_create >>
  disch_then (qspec_then `venom_create_request t value off sz salt` mp_tac) >>
  simp[] >> strip_tac >> gvs[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_delegate_state:
  le_padded_control V s t ==>
  make_venom_delegatecall_state s target gas data code static =
  make_venom_delegatecall_state t target gas data code static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def,
       le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
       venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

Theorem le_padded_extract_result:
  le_padded_control V s t ==>
  OPTREL (\p q. FST p = FST q /\ le_padded_control V (SND p) (SND q))
    (extract_venom_result s ov ro rz rr) (extract_venom_result t ov ro rz rr)
Proof
  strip_tac >>
  `!bytes i. read_memory i 1 (write_memory_with_expansion ro bytes s) =
              read_memory i 1 (write_memory_with_expansion ro bytes t)` by
    metis_tac[le_padded_control_write_memory, le_padded_control_def,
              padded_exec_equiv_read_memory] >>
  Cases_on `rr` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  PairCases_on `h` >> simp[] >>
  Cases_on `x0` >> simp[]
  >- (gvs[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
           read_memory_def, execution_frame_def, venom_state_component_equality,
           ] >> rpt strip_tac >> gvs[]) >>
  Cases_on `y` >> simp[] >>
  gvs[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
      read_memory_def, execution_frame_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_padded_exec_delegatecall:
  le_padded_control V s t ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (exec_delegatecall i s gas addr ao az ro rz)
    (exec_delegatecall i t gas addr ao az ro rz)
Proof
  strip_tac >>
  `venom_call_request s addr 0w ao az F =
   venom_call_request t addr 0w ao az F` by
    metis_tac[le_padded_requests] >>
  simp[exec_delegatecall_def] >> rpt (pairarg_tac >> simp[]) >>
  drule le_padded_consume_call >>
  disch_then (qspecl_then [`w2n rz`,
    `venom_call_request t addr 0w ao az F with cr_kind := DelegateMessageCall`,
    `w2n ro`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def, le_padded_control_update_var]
QED

Theorem le_padded_call:
  i.inst_opcode = CALL /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "gas r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "addr r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "value r3"] >> simp[lift_result_def] >>
  namedCases_on `r3` ["", "ao r4"] >> simp[lift_result_def] >>
  namedCases_on `r4` ["", "az r5"] >> simp[lift_result_def] >>
  namedCases_on `r5` ["", "ro r6"] >> simp[lift_result_def] >>
  namedCases_on `r6` ["", "rz r7"] >> simp[lift_result_def] >>
  Cases_on `r7` >> simp[lift_result_def] >>
  `eval_operand gas s = eval_operand gas t /\
   eval_operand addr s = eval_operand addr t /\
   eval_operand value s = eval_operand value t /\
   eval_operand ao s = eval_operand ao t /\
   eval_operand az s = eval_operand az t /\
   eval_operand ro s = eval_operand ro t /\
   eval_operand rz s = eval_operand rz t` by simp[] >>
  Cases_on `eval_operand gas t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand addr t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand value t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand ao t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand az t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand ro t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand rz t` >> gvs[lift_result_def] >>
  IF_CASES_TAC >-
    (simp[lift_result_def] >> metis_tac[le_padded_terminal_updates, le_padded_control_def]) >>
  simp[le_padded_exec_ext_call]
QED

Theorem le_padded_static_delegate:
  MEM i.inst_opcode [STATICCALL; DELEGATECALL] /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >> Cases_on `i.inst_opcode` >> gvs[] >>
  simp[step_inst_base_opcode_eqs] >>
  namedCases_on `i.inst_operands` ["", "gas r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "addr r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "ao r3"] >> simp[lift_result_def] >>
  namedCases_on `r3` ["", "az r4"] >> simp[lift_result_def] >>
  namedCases_on `r4` ["", "ro r5"] >> simp[lift_result_def] >>
  namedCases_on `r5` ["", "rz r6"] >> simp[lift_result_def] >>
  Cases_on `r6` >> simp[lift_result_def] >>
  `eval_operand gas s = eval_operand gas t /\
   eval_operand addr s = eval_operand addr t /\
   eval_operand ao s = eval_operand ao t /\
   eval_operand az s = eval_operand az t /\
   eval_operand ro s = eval_operand ro t /\
   eval_operand rz s = eval_operand rz t` by simp[] >>
  Cases_on `eval_operand gas t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand addr t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand ao t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand az t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand ro t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand rz t` >> gvs[lift_result_def] >>
  simp[le_padded_exec_ext_call, le_padded_exec_delegatecall]
QED

Theorem le_padded_create:
  i.inst_opcode = CREATE /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule le_padded_operands_eq >> simp[]) >>
  simp[step_inst_base_opcode_eqs] >>
  IF_CASES_TAC >-
    (simp[lift_result_def] >> metis_tac[le_padded_terminal_updates, le_padded_control_def]) >>
  namedCases_on `i.inst_operands` ["", "value r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "off r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "sz r3"] >> simp[lift_result_def] >>
  Cases_on `r3` >> simp[lift_result_def] >>
  `eval_operand value s = eval_operand value t /\
   eval_operand off s = eval_operand off t /\
   eval_operand sz s = eval_operand sz t` by simp[] >>
  Cases_on `eval_operand value t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand off t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >> gvs[lift_result_def] >>
  simp[le_padded_exec_create]
QED

Theorem le_padded_create2:
  i.inst_opcode = CREATE2 /\ le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[le_padded_control_def, padded_exec_equiv_def, execution_frame_def,
        venom_state_component_equality] >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule le_padded_operands_eq >> simp[]) >>
  simp[step_inst_base_opcode_eqs] >>
  IF_CASES_TAC >-
    (simp[lift_result_def] >> metis_tac[le_padded_terminal_updates, le_padded_control_def]) >>
  namedCases_on `i.inst_operands` ["", "value r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "off r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "sz r3"] >> simp[lift_result_def] >>
  namedCases_on `r3` ["", "salt r4"] >> simp[lift_result_def] >>
  Cases_on `r4` >> simp[lift_result_def] >>
  `eval_operand value s = eval_operand value t /\
   eval_operand off s = eval_operand off t /\
   eval_operand sz s = eval_operand sz t /\
   eval_operand salt s = eval_operand salt t` by simp[] >>
  Cases_on `eval_operand value t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand off t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand sz t` >> gvs[lift_result_def] >>
  Cases_on `eval_operand salt t` >> gvs[lift_result_def] >>
  simp[le_padded_exec_create]
QED

Theorem le_padded_noncall_step:
  le_padded_control V s t /\
  (!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t) /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> MEMTOP ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  strip_tac >>
  `padded_exec_equiv V s t` by gvs[le_padded_control_def] >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule le_padded_operand_agreement >> metis_tac[]) >>
  `!ops. EVERY (\op. MEM op i.inst_operands) ops ==>
     eval_operands ops s = eval_operands ops t` by
    (rpt strip_tac >> irule le_padded_operands_agreement >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule le_padded_operands_agreement >> metis_tac[]) >>
  Cases_on `i.inst_opcode` >> gvs[] >>
  FIRST_PROVE (map (fn th => irule th >> simp[])
    [le_padded_arithmetic, le_padded_context_reads, le_padded_store_ops,
     le_padded_mcopy_op, le_padded_istore_op, le_padded_return_revert,
     le_padded_sha3, le_padded_simple_terminal, le_padded_assertions,
     le_padded_jmp, le_padded_djmp, le_padded_jnz, le_padded_internal_return,
     le_padded_assign, le_padded_context_copy, le_padded_extcodecopy,
     le_padded_fmp_reads, le_padded_fmp_write, le_padded_params,
     le_padded_bump, le_padded_alloca, le_padded_selfdestruct,
     le_padded_invalid, le_padded_dret, le_padded_log, le_padded_call,
     le_padded_static_delegate, le_padded_create, le_padded_create2])
QED
