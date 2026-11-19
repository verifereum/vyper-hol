Theory gasFocusConcretizeHistoryFmp
Ancestors
  concretizePtrCoverageStaticMem concretizePtrChronologicalHistory
  concretizePtrOperationalOpcodes gasFocusChronologicalCut
  concretizeLayoutCutSafe o1SafeUpto venomExecSemantics venomExecProofs
  venomWf venomState venomInst memLocDefs list finite_map

(* Earlier observations stay in the current gas cut: monotonic remaining
   readings are used backwards, never restored from a saved caller. *)
Theorem ptr_focus_coverage_history_fmp:
  !vs0 ctx h a. ptr_chrono_history vs0 ctx h a ==>
    gas_cut n vs0 a.po_state /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) ctx.ctx_functions /\
    (!ht at. ptr_chrono_history vs0 ctx ht at /\ gas_cut n vs0 at.po_state ==>
       w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp \/
       ?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
         revert_forward_pair bb i j /\
         i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j) ==>
    w2n a.po_state.vs_initial_fmp <= w2n a.po_state.vs_fmp
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      `ptr_chrono_history vs0 ctx [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
         (ptr_observe [] [] FEMPTY entry_taint fn inst s1)` by
        metis_tac[ptr_chrono_history_rules] >>
      qpat_x_assum `!ht at. _` (drule_all_then
        (DISJ_CASES_THEN2 ACCEPT_TAC strip_assume_tac)) >>
      gvs[ptr_observe_def] >>
      `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
      `ALL_DISTINCT (fn_labels fn)` by fs[EVERY_MEM] >>
      drule_all enters_block_before_revert_window >> decide_tac) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `ptr_chrono_step ctx a b` >>
  rename1 `ptr_chrono_history vs0 ctx h a` >>
  `gas_cut n vs0 a.po_state` by
    (drule ptr_chrono_step_readings_le >>
     metis_tac[gas_cut_readings_mono]) >>
  `w2n a.po_state.vs_initial_fmp <= w2n a.po_state.vs_fmp` by
    (first_x_assum irule >> metis_tac[]) >>
  `ptr_chrono_history vs0 ctx (h ++ [b]) b` by
    metis_tac[ptr_chrono_history_rules] >>
  qpat_x_assum `!ht at. _` (drule_all_then
    (DISJ_CASES_THEN2 ACCEPT_TAC strip_assume_tac)) >>
  `ALL_DISTINCT (fn_labels b.po_fn)` by
    (drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> fs[EVERY_MEM]) >>
  qpat_assum `ptr_chrono_history vs0 ctx h a`
    (mp_then Any strip_assume_tac ptr_chrono_history_suspended_invokes) >>
  drule_all ptr_chrono_step_window_fmp >> strip_tac >> simp[]
QED
