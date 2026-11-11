(* ptrSafeRun's check is monotone in the dead bytes: a run whose taint stays
 * inside D stays inside any D' that contains D at every place.
 * TOP-LEVEL: ptr_safe_dead_mono, ptr_safe_run_dead_mono.
 *)
Theory ctorDeployMemoryRunPtrMono
Ancestors
  ptrSafeRun ptrDiscipline

Theorem ptr_inst_ok_dead_mono:
  !D D' lo fuel ctx fn G tn inst s.
    ptr_inst_ok D lo fuel ctx fn G tn inst s /\
    (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
    (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
    (!i. D.d_imm i SUBSET D'.d_imm i) /\
    (!r. D.d_ret r SUBSET D'.d_ret r) ==>
    ptr_inst_ok D' lo fuel ctx fn G tn inst s
Proof
  rw[ptr_inst_ok_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem ptr_safe_dead_mono:
  (!D lo fuel ctx fn PG G tn inst s D'.
     ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
     (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
     (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
     (!i. D.d_imm i SUBSET D'.d_imm i) /\
     (!r. D.d_ret r SUBSET D'.d_ret r) ==>
     ptr_safe_step D' lo fuel ctx fn PG G tn inst s) /\
  (!D lo fuel ctx fn PG G tn bb s D'.
     ptr_safe_block D lo fuel ctx fn PG G tn bb s /\
     (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
     (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
     (!i. D.d_imm i SUBSET D'.d_imm i) /\
     (!r. D.d_ret r SUBSET D'.d_ret r) ==>
     ptr_safe_block D' lo fuel ctx fn PG G tn bb s) /\
  (!D lo fuel ctx fn PG G tn s D'.
     ptr_safe_blocks D lo fuel ctx fn PG G tn s /\
     (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
     (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
     (!i. D.d_imm i SUBSET D'.d_imm i) /\
     (!r. D.d_ret r SUBSET D'.d_ret r) ==>
     ptr_safe_blocks D' lo fuel ctx fn PG G tn s)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC [ptr_safe_step_def] >> strip_tac >>
      conj_tac >- (irule ptr_inst_ok_dead_mono >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
      BasicProvers.every_case_tac >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC [ptr_safe_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      Cases_on `step_inst fuel ctx inst s` >> simp[] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ _` mp_tac >>
  ONCE_REWRITE_TAC [ptr_safe_blocks_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem ptr_safe_run_dead_mono:
  !D D' lo fuel ctx fn PG G tn s.
    ptr_safe_run D lo fuel ctx fn PG G tn s /\
    (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
    (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
    (!i. D.d_imm i SUBSET D'.d_imm i) /\
    (!r. D.d_ret r SUBSET D'.d_ret r) ==>
    ptr_safe_run D' lo fuel ctx fn PG G tn s
Proof
  rw[ptr_safe_run_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  metis_tac[ptr_safe_dead_mono]
QED
