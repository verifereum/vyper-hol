Theory deployOutcomesFreeBodyGenerators
Ancestors
  ctorCallFreeRules
  deployOutcomesFreeGenerators exprLowering context
  ctorCallFreeStmtStorage ctorCallFreeValues

Theorem outcomes_free_dynarray_append:
  (!opc. MEM opc [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD; CALLDATALOAD;
     MSTORE; SSTORE; TSTORE; ISTORE; INVALID; LT; ASSERT; ADD; MUL] ==> P opc) /\
  (!ce a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce a b ty sty st)))) /\
  (!ce src slot ty tr st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots ce src slot ty tr st)))) ==>
  !ce a b ws sz ty sty cap prim loc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_dynarray_append ce a b ws sz ty sty cap prim loc s)))
Proof
  strip_tac >> rpt gen_tac >> qid_spec_tac `s` >>
  simp[compile_dynarray_append_def] >>
  rpt (FIRST [ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
    ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `s`,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        every_state_insts_return,
      outcomes_free_ptr_load, outcomes_free_ptr_store, outcomes_free_imm_store_words]),
    first_assum irule])
QED
