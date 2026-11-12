Theory deployOutcomesFreeStmtAssign
Ancestors
  deployOutcomesFreeLowering stmtLowering compileEnv list

Theorem outcomes_free_compile_assign_value:
  EVERY P [MSTORE; SSTORE; TSTORE; MLOAD; INVALID] /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce a b ty sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty s)))) /\
  (!ce a ty b sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory_typed ce a ty b sty s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_copy_memory a b n s)))) /\
  (!a b ew ems tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_to_storage a b ew ems tr s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_storage a b n s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_transient a b n s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_word imm a b s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_immutable_bytestring imm a b s)))) /\
  (!imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_words imm a b n k s)))) ==>
  !ce dst loc value prim src_loc dst_ty src_ty da_info size s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts
      (SND (compile_assign_value ce dst loc value prim src_loc dst_ty src_ty da_info size s)))
Proof
  simp[EVERY_DEF] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `da_info` >>
  Cases_on `loc` >> simp[compile_assign_value_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  simp[outcomes_free_return, outcomes_free_emit_ops] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
              irule outcomes_free_ignore_bind >> conj_tac,
              irule outcomes_free_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  rpt IF_CASES_TAC >> simp[outcomes_free_return, outcomes_free_emit_ops] >>
  PairCases_on `x` >> simp[]
QED
