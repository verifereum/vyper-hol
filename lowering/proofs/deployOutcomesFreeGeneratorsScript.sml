Theory deployOutcomesFreeGenerators
Ancestors
  deployOutcomesFreeLowering exprLowering context emitHelper compileEnv
  exprBopLowering list pair

Theorem outcomes_free_as_ptr_val:
  SND (as_ptr_val ty loc m) = SND m
Proof
  Cases_on `m` >> simp[as_ptr_val_def]
QED

Theorem outcomes_free_alloc_buffer:
  P ALLOCA /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_alloc_buffer sz s)))
Proof
  rpt strip_tac >> simp[compile_alloc_buffer_def] >>
  irule outcomes_free_bind >> simp[outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_imm_load:
  P ADD /\ P ILOAD /\ P DLOAD /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_load_word ctor imm off s)))
Proof
  rpt strip_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, outcomes_free_emit_ops] >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_ptr_load:
  P ADD /\ P ILOAD /\ P DLOAD /\ P MLOAD /\ P SLOAD /\
  P TLOAD /\ P CALLDATALOAD /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_load ctor imm loc off s)))
Proof
  rpt strip_tac >> Cases_on `loc` >>
  simp[compile_ptr_load_def, outcomes_free_emit_ops, outcomes_free_imm_load]
QED

Theorem outcomes_free_imm_store:
  P ADD /\ P ISTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_word imm off v s)))
Proof
  rpt strip_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, outcomes_free_emit_ops] >>
  irule outcomes_free_bind >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_ptr_store:
  P ADD /\ P ISTORE /\ P INVALID /\ P MSTORE /\ P SSTORE /\ P TSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_store ctor imm loc off v s)))
Proof
  rpt strip_tac >> Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, outcomes_free_emit_ops, outcomes_free_imm_store]
QED

Theorem outcomes_free_copy_memory:
  P MCOPY /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory dst src sz s)))
Proof
  Cases_on `sz` >> simp[compile_copy_memory_def, outcomes_free_return,
    outcomes_free_emit_ops]
QED

Theorem outcomes_free_word_copy_base:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords load store ctor imm s)))
Proof
  strip_tac >> simp[compile_word_copy_loop_base_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
               outcomes_free_fresh, outcomes_free_new_block,
               outcomes_free_ptr_load, outcomes_free_ptr_store]),
       gen_tac, strip_tac, irule outcomes_free_bind,
       irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  gvs[]
QED

Theorem outcomes_free_word_copy:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords load store ctor s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_op src dst nwop load store ctor s)))
Proof
  strip_tac >> simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def] >>
  conj_tac >> irule outcomes_free_word_copy_base >> simp[]
QED

Theorem outcomes_free_lit_offset:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_lit_byte_offset op off s)))
Proof
  rpt strip_tac >> Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, outcomes_free_return, outcomes_free_emit_ops]
QED

Theorem outcomes_free_imm_copy:
  !n off s. P ADD /\ P ILOAD /\ P DLOAD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off s)))
Proof
  Induct_on `n` >> rpt strip_tac >>
  simp[compile_imm_copy_to_memory_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_lit_offset,
          outcomes_free_imm_load, outcomes_free_emit_ops]),
       gen_tac, strip_tac, irule outcomes_free_bind,
       irule outcomes_free_ignore_bind, conj_tac, first_assum irule])
QED
