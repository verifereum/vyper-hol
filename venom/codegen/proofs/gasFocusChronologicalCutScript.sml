Theory gasFocusChronologicalCut
Ancestors
  concretizePtrChronologicalHistory concretizeLayoutCutSafe
  o1SafeUpto gasOracleReplay venomInst list arithmetic

(* Chronological observations retain completed activations; returns consume
   the callee's readings rather than restoring the saved caller's oracle. *)
Theorem ptr_chrono_step_readings_le:
  !C a b. ptr_chrono_step C a b ==>
    LENGTH b.po_state.vs_gas_readings <= LENGTH a.po_state.vs_gas_readings
Proof
  ho_match_mp_tac ptr_chrono_step_ind >>
  simp[ptr_observe_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (irule step_inst_noninvoke_readings_le >> metis_tac[])
  >- (drule enters_block_readings >> simp[] >> strip_tac >>
      irule step_inst_noninvoke_readings_le >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> gvs[is_terminator_def]) >>
      metis_tac[])
  >- (drule enters_block_readings >> drule gas_setup_callee_readings >>
      simp[]) >>
  metis_tac[return_readings_le]
QED

Theorem ptr_chrono_history_readings_le:
  !vs C h a. ptr_chrono_history vs C h a ==>
    EVERY (\b. LENGTH a.po_state.vs_gas_readings <=
               LENGTH b.po_state.vs_gas_readings) h
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[EVERY_APPEND] >>
  drule ptr_chrono_step_readings_le >>
  gvs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem ptr_chrono_history_cut:
  ptr_chrono_history vs C h a /\ gas_cut n vs a.po_state ==>
    EVERY (\b. gas_cut n vs b.po_state) h
Proof
  strip_tac >> drule ptr_chrono_history_readings_le >>
  simp[EVERY_MEM] >> metis_tac[gas_cut_readings_mono]
QED

Theorem ptr_chrono_saved_callers_readings_le:
  !vs C h a. ptr_chrono_history vs C h a ==>
    EVERY (\f. LENGTH a.po_state.vs_gas_readings <=
               LENGTH f.cf_state.vs_gas_readings) a.po_stack
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> conj_tac
  >- simp[ptr_observe_def] >>
  rpt gen_tac >> strip_tac >>
  drule ptr_chrono_step_readings_le >> strip_tac >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >>
  irule LESS_EQ_TRANS >> qexists_tac `LENGTH s.vs_gas_readings` >> simp[]
QED

Theorem ptr_chrono_saved_callers_cut:
  ptr_chrono_history vs C h a /\ gas_cut n vs a.po_state ==>
    EVERY (\f. gas_cut n vs f.cf_state) a.po_stack
Proof
  strip_tac >> drule ptr_chrono_saved_callers_readings_le >>
  simp[EVERY_MEM] >> metis_tac[gas_cut_readings_mono]
QED
