Theory gasFocusConcretizeHistoricalCut
Ancestors
  gasFocusChronologicalCut concretizeLayoutCutSafe
  concretizePtrHistoricalPlacement concretizePtrExecutedCoverage
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  concretizePtrPrefixLedger concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrStagePlacements
  concretizePtrOwnerPath o1PassContract o1SafeUpto o1ScheduleDecompHelpers
  venomWf venomInst ptrDiscipline finite_map list arithmetic

Theorem ptr_source_ownership_erases_upto:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_discipline_upto lo n C vs /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  gas_cut n vs a.po_state ==>
  ptr_params_erases (dyn_floor C vs) births PT a.po_params /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  ptr_saved_erases (dyn_floor C vs) births saved a.po_stack
Proof
  strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_sound >> strip_tac >>
  `EVERY (\obs. ctx_has_dalloca C ==> allocas_below_fmp obs.po_state) h` by
    (drule_all ptr_chrono_history_cut >> simp[EVERY_MEM] >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[EVERY_MEM, ptr_observation_reachable_def] >> strip_tac >>
     rpt strip_tac >>
     qpat_assum `!obs. MEM obs h ==> gas_cut _ _ _` (drule_then assume_tac) >>
     qpat_assum `!obs. MEM obs h ==> frame_reachable _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all ptr_discipline_upto_at >> simp[]) >>
  fs[ptr_discipline_upto_def] >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_history_erases >> simp[]
QED
