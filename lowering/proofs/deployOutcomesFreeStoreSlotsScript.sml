Theory deployOutcomesFreeStoreSlots
Ancestors
  deployOutcomesFreeGenerators deployOutcomesFreeLowering context

Theorem outcomes_free_store_slots_mutual:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
    SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE; TSTORE;
    SHR; LT; ISZERO] ==> P opc) ==>
  (!ce src slot ty tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots ce src slot ty tr s)))) /\
  (!ce src slot members mo so tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots_members ce src slot members mo so tr s)))) /\
  (!ce src slot elem cnt tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_elements_to_slots ce src slot elem cnt tr s))))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  ho_match_mp_tac compile_store_slots_ind >> rpt strip_tac >>
  simp[Once compile_store_slots_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops,
    outcomes_free_fresh, outcomes_free_new_block, outcomes_free_lit_offset,
    outcomes_free_bytestring_word_count,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_slot_copies,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_word_copy]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC,
    first_assum (fn th => irule th >> simp[] >> NO_TAC)]) >>
  Cases_on `ty` >> gvs[] >>
  TRY (rename1 `ArrayT elem kind` >> Cases_on `kind` >> gvs[]) >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, first_assum (fn th => irule th >> simp[] >> NO_TAC)]) >>
  first_x_assum irule >> simp[]
QED
