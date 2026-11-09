Theory concretizePtrHistoryCoverage
Ancestors
  concretizePtrContextRoot concretizePtrChronologicalHistory
  concretizePtrPairedRoot concretizePtrForwardingTransport
  concretizePtrOperationalOpcodes venomWf unitLabelMapIdentity
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace contextCodegenRel venomExecSemantics
  venomState venomInst venomInstProps venomExecProofs stepWriteFootprintForward
  list finite_map arithmetic

Theorem ptr_paired_history_forwarding_transport[local]:
  EVERY fn_inst_wf C.ctx_functions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\ in_revert_forward a.po_fn a.po_state ==>
  in_revert_forward at.po_fn at.po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_reachable >>
  strip_tac >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  irule ptr_paired_cursor_forwarding >>
  qexistsl_tac [`a`, `lp`] >> simp[EVERY_MEM] >>
  rpt strip_tac >>
  `inst_wf inst` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def]
QED

Theorem ptr_paired_history_window_step[local]:
  EVERY (\g. ALL_DISTINCT (fn_labels g)) ctx.ctx_functions /\
  ptr_chrono_history vs ctx h a /\ ptr_chrono_step ctx a b /\
  (in_revert_forward a.po_fn a.po_state \/
   (?bb i j. lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
     revert_forward_pair bb i j /\
     i < a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx <= j)) ==>
  ?bb i j. lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\
    i < b.po_state.vs_inst_idx /\ b.po_state.vs_inst_idx <= j
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> fs[EVERY_MEM] >> metis_tac[]) >>
  `?win p q. lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME win /\
    revert_forward_pair win p q /\
    p <= a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx <= q` by
    (gvs[in_revert_forward_def, revert_forward_at_def] >>
     metis_tac[revert_forward_pair_def, LESS_OR_EQ]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
     simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
     gvs[ptr_observe_def]) >>
  `get_instruction win a.po_state.vs_inst_idx = SOME a.po_inst` by
    (fs[active_inst_def, fn_labels_def] >>
     rename1 `MEM activebb a.po_fn.fn_blocks` >>
     `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME activebb` by
       (irule MEM_lookup_block >> simp[]) >>
     gvs[get_instruction_def]) >>
  `a.po_state.vs_inst_idx <> q` by
    (strip_tac >>
     `a.po_inst.inst_opcode = REVERT` by gvs[revert_forward_pair_def] >>
     qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
     simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
     gvs[ptr_observe_def, is_terminator_def] >>
     metis_tac[step_revert_no_normal]) >>
  `a.po_inst.inst_opcode = ASSIGN \/
   a.po_inst.inst_opcode = RETURNDATACOPY` by
    (Cases_on `a.po_state.vs_inst_idx = p` >>
     gvs[revert_forward_pair_def] >>
     `p < a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx < q` by decide_tac >>
     metis_tac[]) >>
  `b.po_fn = a.po_fn /\
   b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
   b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx` by
    (qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
     simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
     gvs[ptr_observe_def, is_terminator_def] >>
     gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
     simp[update_var_def, write_memory_with_expansion_def, write_memory_def]) >>
  qexistsl_tac [`win`, `p`, `q`] >> simp[]
QED

(* Conditional integration only: the universal step premise is not discharged.
   A history that runs a revert forwarding's RETURNDATACOPY leaves the paired
   prefix there and stays inside the forwarding window up to its REVERT. *)
Theorem ptr_paired_history_coverage:
  C.ctx_entry = Ct.ctx_entry /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\ vs.vs_vars = FEMPTY /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  (!h a ht at done tokens registry births PT TG saved entries H calls ws zt.
    ptr_paired_prefix R lp positions lo vs C Ct
      h a ht at done tokens registry births PT TG saved entries H calls ws /\
    a.po_inst.inst_opcode <> NOP /\
    at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
    ~in_revert_forward a.po_fn a.po_state /\
    ptr_chrono_step Ct at zt ==>
    ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
      delta <> [] /\ LENGTH snapshots = LENGTH delta /\
      ptr_paired_prefix R lp positions lo vs C Ct
        (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
        tokens' registry' births' PT' TG' saved' entries'
        (H ++ snapshots) calls' ws' /\
      z.po_inst.inst_opcode <> NOP /\
      zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst) ==>
  !ht at. ptr_chrono_history vs Ct ht at ==>
    (?h a done tokens registry births PT TG saved entries H calls ws.
      ptr_paired_prefix R lp positions lo vs C Ct
        h a ht at done tokens registry births PT TG saved entries H calls ws /\
      a.po_inst.inst_opcode <> NOP /\
      at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
    (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
      revert_forward_pair bb i j /\
      i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)
Proof
  disch_tac >> rpt gen_tac >> pop_assum mp_tac >>
  once_rewrite_tac[AND_IMP_INTRO] >>
  once_rewrite_tac[CONJ_COMM] >> pure_once_rewrite_tac[GSYM AND_IMP_INTRO] >>
  Induct_on `ptr_chrono_history vs Ct ht at` >>
  rpt strip_tac
  >- (disj1_tac >>
      `ptr_chrono_history vs Ct
         [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
         (ptr_observe [] [] FEMPTY entry_taint fn inst s1)` by
        metis_tac[ptr_chrono_history_rules] >>
      `(ptr_observe [] [] FEMPTY entry_taint fn inst s1).po_stack = []` by
        simp[ptr_observe_def] >>
      drule_all ptr_paired_context_root >>
      disch_then (qspec_then `lo` strip_assume_tac) >>
      fs[ptr_observe_def] >>
      qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >>
  qpat_x_assum `_ ==> _ \/ _` mp_tac >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac
  >- (Cases_on `in_revert_forward a.po_fn a.po_state`
      >- (disj2_tac >>
          `EVERY fn_inst_wf C.ctx_functions` by
            (fs[EVERY_MEM] >> metis_tac[]) >>
          drule_all ptr_paired_history_forwarding_transport >> strip_tac >>
          metis_tac[ptr_paired_history_window_step]) >>
      disj1_tac >>
      qpat_x_assum `!h a ht at done tokens registry births PT TG saved entries H calls ws zt. _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >>
  disj2_tac >>
  `?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ i < at.po_state.vs_inst_idx /\
    at.po_state.vs_inst_idx <= j` by metis_tac[] >>
  drule ptr_paired_history_window_step >>
  disch_then drule >> disch_then drule >> simp[] >> metis_tac[]
QED
