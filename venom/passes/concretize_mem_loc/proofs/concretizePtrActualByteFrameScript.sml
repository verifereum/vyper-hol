Theory concretizePtrActualByteFrame
Ancestors concretizePtrOperationalBytes concretizePtrChronologicalHistory
  concretizePtrLifetime calleeTransport opcodeClass
  regularCallEmitSim stepWriteFootprintBase ptrDiscipline venomMemProps venomExecSemantics
  venomCallOracleDefs codegenRel venomState venomInst list pred_set arithmetic

Theorem ptr_extract_venom_result_actual_byte_frame:
  extract_venom_result s output ro rz result = SOME (value,t) /\
  ~(ro <= x /\ x < ro + MIN rz (LENGTH t.vs_returndata)) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >> drule extract_venom_result_memory >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  irule write_memory_byte_frame >>
  qexists `LENGTH (TAKE rz t.vs_returndata)` >>
  gvs[LENGTH_TAKE_EQ, MIN_DEF]
QED

Theorem ptr_exec_ext_call_actual_byte_frame:
  exec_ext_call inst s gas addr value ao az ro rz static = OK t /\
  ~(w2n ro <= x /\ x < w2n ro + MIN (w2n rz) (LENGTH t.vs_returndata)) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  simp[exec_ext_call_def, consume_call_outcome_eq] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n ro) bytes s` >>
  irule write_memory_byte_frame >> qexists `LENGTH bytes` >>
  gvs[Abbr `bytes`, LENGTH_TAKE_EQ, MIN_DEF]
QED

Theorem ptr_exec_delegatecall_actual_byte_frame:
  exec_delegatecall inst s gas addr ao az ro rz = OK t /\
  ~(w2n ro <= x /\ x < w2n ro + MIN (w2n rz) (LENGTH t.vs_returndata)) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  simp[exec_delegatecall_def, consume_call_outcome_eq] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n ro) bytes s` >>
  irule write_memory_byte_frame >> qexists `LENGTH bytes` >>
  gvs[Abbr `bytes`, LENGTH_TAKE_EQ, MIN_DEF]
QED

Theorem ptr_step_inst_base_OK_actual_byte_frame:
  step_inst_base inst s = OK t /\
  x NOTIN range_bytes (step_writes inst s t) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
            inst.inst_opcode = DELEGATECALL`
  >- (gvs[] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      gvs[step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
      metis_tac[ptr_exec_ext_call_actual_byte_frame,
                ptr_exec_delegatecall_actual_byte_frame]) >>
  irule step_inst_base_OK_byte_frame >>
  qexists `inst` >> simp[] >>
  gvs[step_writes_def, range_bytes_def] >> metis_tac[ADD_COMM]
QED

Theorem ptr_chrono_step_actual_byte_frame:
  !ctx a z. ptr_chrono_step ctx a z ==>
  !x. x NOTIN range_bytes (step_writes a.po_inst a.po_state z.po_state) ==>
    read_byte x z.po_state.vs_memory = read_byte x a.po_state.vs_memory
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >>
  simp[ptr_observe_def] >> rpt strip_tac
  >- (gvs[step_inst_non_invoke] >>
      irule ptr_step_inst_base_OK_actual_byte_frame >>
      qexists `inst` >> simp[] >> gvs[step_writes_def])
  >- (`inst.inst_opcode <> CALL /\ inst.inst_opcode <> STATICCALL /\
       inst.inst_opcode <> DELEGATECALL /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      gvs[step_inst_non_invoke, step_writes_def] >>
      drule enters_block_memory >> strip_tac >> asm_rewrite_tac[] >>
      irule step_inst_base_OK_byte_frame >>
      qexists `inst` >> simp[] >> gvs[range_bytes_def] >> metis_tac[ADD_COMM])
  >- (drule setup_callee_shared_fields >> strip_tac >>
      drule enters_block_memory >> simp[]) >>
  `rinst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[step_inst_def, AllCaseEqs()]) >>
  gvs[step_inst_non_invoke] >>
  `MEM rinst.inst_opcode [RET;RETFMP;DRET]` by
    (drule step_inst_base_intret_opcodes >> simp[] >> metis_tac[]) >>
  gvs[step_writes_def] >>
  drule bind_outputs_shared_fields >> simp[] >> strip_tac >>
  irule step_inst_base_IntRet_byte_frame >>
  qexistsl [`rinst`, `ret`] >> gvs[range_bytes_def] >> metis_tac[ADD_COMM]
QED

Theorem ptr_chrono_history_actual_byte_frame:
  ptr_chrono_history vs0 ctx h a /\ SUC k < LENGTH h /\
  x NOTIN range_bytes (step_writes (EL k h).po_inst
    (EL k h).po_state (EL (SUC k) h).po_state) ==>
  read_byte x (EL (SUC k) h).po_state.vs_memory =
    read_byte x (EL k h).po_state.vs_memory
Proof
  metis_tac[ptr_chrono_history_adjacent, ptr_chrono_step_actual_byte_frame]
QED

Theorem ptr_chrono_history_actual_interval_byte_frame:
  !hi lo. ptr_chrono_history vs0 ctx h a /\
    lo <= hi /\ hi < LENGTH h /\
    (!k. lo <= k /\ k < hi ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst
        (EL k h).po_state (EL (SUC k) h).po_state)) ==>
    read_byte x (EL hi h).po_state.vs_memory =
      read_byte x (EL lo h).po_state.vs_memory
Proof
  Induct >> rpt strip_tac
  >- (`lo = 0` by decide_tac >> simp[]) >>
  Cases_on `lo = SUC hi` >- simp[] >>
  `lo <= hi` by decide_tac >>
  `read_byte x (EL (SUC hi) h).po_state.vs_memory =
   read_byte x (EL hi h).po_state.vs_memory` by
    (irule ptr_chrono_history_actual_byte_frame >> simp[] >> metis_tac[]) >>
  `read_byte x (EL hi h).po_state.vs_memory =
   read_byte x (EL lo h).po_state.vs_memory` by
    (first_x_assum irule >> simp[] >> metis_tac[LESS_TRANS]) >>
  metis_tac[]
QED

Theorem ptr_chrono_history_initial_memory:
  !vs C h endpoint. ptr_chrono_history vs C h endpoint ==>
  (HD h).po_state.vs_memory = vs.vs_memory
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt strip_tac >> drule enters_block_memory >>
      simp[ptr_observe_def]) >>
  rpt strip_tac >> drule ptr_chrono_history_end >> strip_tac >>
  Cases_on `h` >> gvs[]
QED

Theorem ptr_chrono_history_no_actual_write_byte:
  ptr_chrono_history vs C h endpoint /\
  (!k. SUC k < LENGTH h ==> x NOTIN range_bytes
    (step_writes (EL k h).po_inst (EL k h).po_state
      (EL (SUC k) h).po_state)) ==>
  read_byte x endpoint.po_state.vs_memory = read_byte x vs.vs_memory
Proof
  strip_tac >> drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_chrono_history_initial_memory >> strip_tac >>
  `0 < LENGTH h /\ EL (LENGTH h-1) h = endpoint /\ EL 0 h = HD h` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `read_byte x (EL (LENGTH h-1) h).po_state.vs_memory =
   read_byte x (EL 0 h).po_state.vs_memory` suffices_by simp[] >>
  irule ptr_chrono_history_actual_interval_byte_frame >>
  simp[] >> metis_tac[]
QED
