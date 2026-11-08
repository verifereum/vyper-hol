Theory loadElimPaddedNoncall
Ancestors
  loadElimMemoryRel loadElimPaddedSimHelpers venomExecSemantics venomState
  stateFrame stateEquiv list finite_map venomMemProps

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
  (irule le_padded_exec_read0 ORELSE irule le_padded_exec_read1) >>
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

Theorem le_padded_store_ops:
  MEM i.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE] /\
  le_padded_control V s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst_base i s) (step_inst_base i t)
Proof
  Cases_on `i.inst_opcode` >> simp[] >> strip_tac >>
  simp[step_inst_base_opcode_eqs] >> irule le_padded_exec_write2 >>
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
