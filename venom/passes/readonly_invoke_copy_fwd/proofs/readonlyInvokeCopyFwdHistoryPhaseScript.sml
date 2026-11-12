(* Source-only phase ledger.  Raw provenance is deliberately not a relational
   effective environment; byte agreement and translation maps are absent. *)
Theory readonlyInvokeCopyFwdHistoryPhase
Ancestors
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdPlan o1LowerDloadOccurrence
  readonlyInvokeCopyFwdProtectionOrigin finite_map list pred_set

Definition ricf_phase_entry_def:
  ricf_phase_entry vs C ctx0 log stk PG G tn fn s a U B (p,pre) <=>
    ricf_history_cursor vs C ctx0 log p pre PG G tn fn s /\
    (?tail. stk = pre ++ tail) /\
    (if pre = [] then a = p.rpe_owner
     else LENGTH pre <= LENGTH U /\
          (EL (LENGTH pre - 1) U).of_owner = p.rpe_owner) /\
    FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
    FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
    0 < p.rpe_size
End

Definition ricf_source_ledger_def:
  ricf_source_ledger vs C ctx0 log stk PG G tn fn inst s n a U B HP H ledger <=>
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
    EVERY (ricf_phase_entry vs C ctx0 log stk PG G tn fn s a U B) ledger
End

Definition ricf_phase_ranges_def:
  ricf_phase_ranges depth ledger =
    { (p.rpe_db,p.rpe_sb,p.rpe_size) |
      ?pre. MEM (p,pre) ledger /\ LENGTH pre = depth }
End

Definition ricf_phase_stack_ranges_def:
  ricf_phase_stack_ranges stk ledger =
    GENLIST (\k. ricf_phase_ranges (SUC k) ledger) (LENGTH stk)
End

Theorem ricf_source_ledger_occurrence:
  ricf_source_ledger vs C ctx0 log stk PG G tn fn inst s n a U B HP H ledger ==>
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H
Proof
  simp[ricf_source_ledger_def]
QED

Theorem ricf_source_ledger_empty:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  ricf_source_ledger vs C ctx0 log stk PG G tn fn inst s n a U B HP H []
Proof
  simp[ricf_source_ledger_def]
QED

Theorem ricf_phase_entry_next:
  ricf_phase_entry vs C ctx0 log stk PG G tn fn s a U B entry /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
  step_inst fuel C inst s = OK u ==>
  ricf_phase_entry vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) entry
Proof
  Cases_on `entry` >> simp[ricf_phase_entry_def, occurrence_sites_step_def] >>
  metis_tac[ricf_history_cursor_next]
QED

Theorem ricf_source_ledger_next:
  ricf_source_ledger vs C ctx0 log stk PG G tn fn inst s n a U B HP H ledger /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_source_ledger vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
    (occurrence_sites_step a B inst u) HP (occurrence_step a HP H inst u) ledger
Proof
  simp[ricf_source_ledger_def, EVERY_MEM] >> rpt strip_tac
  >- (irule occ_frame_reachable_next >> metis_tac[]) >>
  irule ricf_phase_entry_next >> metis_tac[]
QED

Theorem ricf_phase_ranges_empty[simp]:
  ricf_phase_ranges depth [] = {}
Proof
  simp[ricf_phase_ranges_def, EXTENSION]
QED

Theorem ricf_phase_ranges_cons:
  ricf_phase_ranges depth ((p,pre)::ledger) =
    (if LENGTH pre = depth then {(p.rpe_db,p.rpe_sb,p.rpe_size)} else {}) UNION
    ricf_phase_ranges depth ledger
Proof
  Cases_on `LENGTH pre = depth` >>
  simp[ricf_phase_ranges_def, EXTENSION] >> metis_tac[]
QED

Theorem ricf_phase_stack_ranges_length[simp]:
  LENGTH (ricf_phase_stack_ranges stk ledger) = LENGTH stk
Proof
  simp[ricf_phase_stack_ranges_def]
QED

(* The origin can have hidden occurrence annotations, but current allocation
   lookups identify its endpoints without inverting numeric addresses. *)
Theorem ricf_history_origin_endpoints:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  occurrence_allocas_ok B p.rpe_owner p.rpe_before ==>
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size)
Proof
  simp[ricf_history_origin_def, ricf_source_copy_payload_def] >>
  rpt strip_tac >> drule occ_frame_reachable_annotation >> strip_tac >>
  gvs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem ricf_source_ledger_activate_origin:
  ricf_source_ledger vs C ctx0 log stk PG G tn p.rpe_fn
    (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before n a U B HP H ledger /\
  ricf_history_origin vs C ctx0 log p stk PG G tn /\
  p.rpe_owner = a /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  active_inst p.rpe_fn (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before /\
  (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode = MCOPY /\
  step_inst fuel C (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before =
    OK p.rpe_after /\
  active_inst p.rpe_fn next
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx) ==>
  ricf_source_ledger vs C ctx0 log stk PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn next
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx) n a U
    (occurrence_sites_step a B (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    HP (occurrence_step a HP H (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (if 0 < p.rpe_size then (p,[])::ledger else ledger)
Proof
  strip_tac >>
  `~is_terminator (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode /\
   (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode <> INVOKE /\
   (ricf_event_copy p.rpe_event p.rpe_block).inst_opcode <> ALLOCA` by
    simp[venomInstTheory.is_terminator_def] >>
  drule_all ricf_source_ledger_next >> strip_tac >>
  Cases_on `0 < p.rpe_size` >> simp[] >>
  gvs[ricf_source_ledger_def, ricf_phase_entry_def, occurrence_sites_step_def] >>
  metis_tac[ricf_history_cursor_activate]
QED

Theorem ricf_source_ledger_activate:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_source_ledger vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H ledger /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?p. p.rpe_event = e /\ p.rpe_block = EL b fn.fn_blocks /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = u /\ p.rpe_owner = a /\
    ricf_history_origin vs C ctx0 log p stk PG G tn /\
    ricf_source_ledger vs C ctx0 log stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
      (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
      HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (if 0 < p.rpe_size then (p,[])::ledger else ledger)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H` by
    metis_tac[ricf_source_ledger_occurrence] >>
  drule_all ricf_located_event_actual_origin >> strip_tac >>
  `occurrence_allocas_ok B p.rpe_owner p.rpe_before` by
    (drule occ_frame_reachable_annotation >>
     simp[occurrence_annotation_ok_def] >> metis_tac[]) >>
  drule_all ricf_history_origin_endpoints >> strip_tac >>
  `(ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY` by
    (`ssa_form fn` by
       (drule occ_frame_reachable_annotation >>
        fs[EVERY_MEM, venomWfTheory.wf_ssa_def]) >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     metis_tac[ricf_event_copy_shape]) >>
  drule_at (Pat `ricf_history_origin _ _ _ _ _ _ _ _ _`)
    ricf_source_ledger_activate_origin >> simp[] >>
  strip_tac >> qexists_tac `p` >> simp[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem ricf_phase_ranges_activation:
  ricf_phase_ranges depth
    (if 0 < p.rpe_size then (p,[])::ledger else ledger) =
  (if 0 < p.rpe_size /\ depth = 0
   then {(p.rpe_db,p.rpe_sb,p.rpe_size)} else {}) UNION
  ricf_phase_ranges depth ledger
Proof
  Cases_on `0 < p.rpe_size` >>
  simp[ricf_phase_ranges_cons] >> Cases_on `depth = 0` >> simp[]
QED

Theorem ricf_phase_stack_ranges_activation:
  ricf_phase_stack_ranges stk
    (if 0 < p.rpe_size then (p,[])::ledger else ledger) =
  ricf_phase_stack_ranges stk ledger
Proof
  simp[ricf_phase_stack_ranges_def] >> irule listTheory.GENLIST_CONG >>
  simp[ricf_phase_ranges_activation]
QED
