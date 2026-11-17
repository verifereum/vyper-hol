Theory deployOutcomesFreeBodyGenerators
Ancestors
  ctorCallFreeRules
  deployOutcomesFreeLowering deployOutcomesFreeGenerators exprLowering context

Theorem outcomes_free_snapshot:
  (!ce v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v st)))) /\
  (!n st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n st)))) /\
  (!ce a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce a b ty sty st)))) ==>
  !ce copy v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_snapshot_vv ce copy v s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> simp[compile_snapshot_vv_def] >>
  IF_CASES_TAC
  >- (irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[outcomes_free_return]) >>
  IF_CASES_TAC >> simp[outcomes_free_return] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[outcomes_free_return] >>
  simp[compile_materialize_vv_def] >> rpt gen_tac >> strip_tac >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[] >> rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[] >> rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> simp[outcomes_free_return]
QED

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
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
      outcomes_free_ptr_load, outcomes_free_ptr_store, outcomes_free_imm_store_words]),
    first_assum irule])
QED
