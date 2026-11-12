Theory deployOutcomesFreeStmtLog
Ancestors
  deployOutcomesFreeLowering stmtLowering list pair

Theorem outcomes_free_compile_log_save_arg:
  (!ce ty vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_materialize_vv ce ty vv s)))) ==>
  !ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_save_arg ce ty op es s)))
Proof
  rpt strip_tac >> simp[compile_log_save_arg_def] >>
  IF_CASES_TAC >- simp[outcomes_free_return] >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_compile_log_topic_ops:
  (!op bs s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_encode_log_topic op bs s)))) ==>
  !ops s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_topic_ops ops s)))
Proof
  strip_tac >> Induct >> simp[compile_log_topic_ops_def, outcomes_free_return] >>
  gen_tac >> ho_match_mp_tac outcomes_free_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac outcomes_free_bind >> simp[outcomes_free_return]
QED

Theorem outcomes_free_compile_log_store_data:
  P ADD /\ P INVALID /\
  (!ce v dst ty src s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_store_memory ce v dst ty src s)))) ==>
  !ops ce tys buf off s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_log_store_data ce ops tys buf off s)))
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `tys` >>
  simp[compile_log_store_data_def, outcomes_free_return]
  >- metis_tac[outcomes_free_emit_ops]
  >- metis_tac[outcomes_free_emit_ops] >>
  qid_spec_tac `s` >> ho_match_mp_tac outcomes_free_bind >> conj_tac
  >- metis_tac[outcomes_free_emit_ops] >>
  gen_tac >> ho_match_mp_tac outcomes_free_ignore_bind >> simp[]
QED

Theorem outcomes_free_compile_revert_with_reason:
  EVERY P [MSTORE; ADD; MLOAD; NOT; AND; MCOPY; REVERT] /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (unwrap_value ce vv s)))) ==>
  !ce vv ty sz s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_revert_with_reason ce vv ty sz s)))
Proof
  simp[EVERY_DEF] >> strip_tac >> ntac 4 gen_tac >>
  simp[compile_revert_with_reason_def] >>
  rpt (FIRST [ho_match_mp_tac outcomes_free_bind >> conj_tac,
              ho_match_mp_tac outcomes_free_ignore_bind >> conj_tac,
              gen_tac]) >>
  metis_tac[outcomes_free_emit_ops]
QED
