Theory concretizePtrHistoryCoverage
Ancestors
  concretizePtrContextRoot concretizePtrChronologicalHistory
  concretizePtrPairedRoot concretizePtrForwardingTransport
  concretizePtrOperationalOpcodes venomWf unitLabelMapIdentity
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace list finite_map

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
  cheat
QED
