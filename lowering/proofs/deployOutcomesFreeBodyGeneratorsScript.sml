Theory deployOutcomesFreeBodyGenerators
Ancestors
  deployOutcomesFreeLowering exprLowering context

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
  >- (irule outcomes_free_bind >> simp[outcomes_free_return]) >>
  IF_CASES_TAC >> simp[outcomes_free_return] >>
  irule outcomes_free_bind >> simp[outcomes_free_return] >>
  simp[compile_materialize_vv_def] >> rpt gen_tac >> strip_tac >>
  irule outcomes_free_bind >> simp[] >> rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[] >> rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_ignore_bind >> simp[outcomes_free_return]
QED

Theorem outcomes_free_dynarray_append:
  P load /\ P store /\ P LT /\ P ASSERT /\ P ADD /\ P MUL /\
  (!ce a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce a b ty sty st)))) /\
  (!a b n loc st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_word_copy_loop a b n LocMemory loc F st)))) ==>
  !ce a b ws sz ty sty cap prim s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_dynarray_append ce a b ws sz ty sty cap prim load store s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> simp[compile_dynarray_append_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC,
    first_assum (fn th => irule th >> simp[] >> NO_TAC)])
QED
