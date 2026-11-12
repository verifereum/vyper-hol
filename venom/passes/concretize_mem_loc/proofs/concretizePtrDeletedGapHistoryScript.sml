Theory concretizePtrDeletedGapHistory
Ancestors concretizePtrDeletedGaps concretizePtrSourceOwnership concretizePtrLedgerAlignment
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrChronologicalHistory contextCodegenRel ptrDiscipline
  venomExecSemantics venomInst venomInstProps list arithmetic finite_map

Definition ptr_gap_next_def:
  ptr_gap_next bb a =
    ptr_observe a.po_stack a.po_params
      (step_prov a.po_params a.po_prov a.po_inst a.po_state)
      (step_taint a.po_inst a.po_state a.po_state a.po_taint)
      a.po_fn (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions)
      (a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)
End

Definition ptr_gap_scan_def:
  (ptr_gap_scan bb 0 a = a) /\
  (ptr_gap_scan bb (SUC n) a = ptr_gap_scan bb n (ptr_gap_next bb a))
End

Theorem ptr_gap_scan_zero:
  ptr_gap_scan bb 0 a = a
Proof
  simp[ptr_gap_scan_def]
QED

Theorem ptr_gap_scan_successor:
  ptr_gap_scan bb (SUC n) a = ptr_gap_scan bb n (ptr_gap_next bb a)
Proof
  simp[ptr_gap_scan_def]
QED

Theorem ptr_gap_tagged_next:
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
  a.po_inst.inst_opcode = NOP ==>
  ptr_tagged_chrono_step C token a (ptr_gap_next bb a)
    PT TG saved PT (step_prov PT TG a.po_inst a.po_state) saved
Proof
  strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac) >>
  `active_inst a.po_fn (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions)
    (a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  `step_inst 0 C a.po_inst a.po_state = OK a.po_state` by
    metis_tac[step_nop_identity] >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ptr_tagged_chrono_step C token
    (ptr_observe a.po_stack a.po_params a.po_prov a.po_taint a.po_fn a.po_inst a.po_state)
    (ptr_gap_next bb a) PT TG saved PT
    (ptr_tagged_step token PT TG a.po_inst a.po_state) saved` by
    (pure_rewrite_tac[ptr_gap_next_def] >>
     irule (cj 1 ptr_tagged_chrono_step_rules) >>
     metis_tac[]) >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state = a` by
    (simp[NoAsms, ptr_observe_def, ptr_observation_component_equality]) >>
  gvs[ptr_tagged_step_def]
QED

Theorem ptr_gap_next_fields:
  (ptr_gap_next bb a).po_fn = a.po_fn /\
  (ptr_gap_next bb a).po_stack = a.po_stack /\
  (ptr_gap_next bb a).po_params = a.po_params /\
  (ptr_gap_next bb a).po_inst = EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions /\
  (ptr_gap_next bb a).po_state =
    (a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)
Proof
  simp[ptr_gap_next_def, ptr_observe_def]
QED

Theorem ptr_gap_scan_fields:
  !n a. (ptr_gap_scan bb n a).po_fn = a.po_fn /\
    (ptr_gap_scan bb n a).po_stack = a.po_stack /\
    (ptr_gap_scan bb n a).po_params = a.po_params /\
    (ptr_gap_scan bb n a).po_state =
      (a.po_state with vs_inst_idx := a.po_state.vs_inst_idx + n) /\
    (0 < n ==> (ptr_gap_scan bb n a).po_inst =
      EL (a.po_state.vs_inst_idx + n) bb.bb_instructions)
Proof
  Induct >> simp[ptr_gap_scan_def, ptr_gap_next_fields, ADD_CLAUSES] >>
  Cases_on `n` >> simp[ptr_gap_scan_def, ptr_gap_next_fields, ADD_CLAUSES]
QED

Definition ptr_gap_tag_scan_def:
  (ptr_gap_tag_scan bb 0 a PT TG = TG) /\
  (ptr_gap_tag_scan bb (SUC n) a PT TG =
    ptr_gap_tag_scan bb n (ptr_gap_next bb a) PT
      (step_prov PT TG a.po_inst a.po_state))
End

Theorem ptr_birth_overlay_idempotent[local]:
  ptr_birth_overlay token A (ptr_birth_overlay token A births) =
  ptr_birth_overlay token A births
Proof
  simp[ptr_birth_overlay_def, FUNION_ASSOC]
QED

Theorem ptr_ownership_overlay_fixed:
  !vs0 C h a tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ptr_birth_overlay (HD tokens) a.po_state.vs_allocas births = births
Proof
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- simp[ptr_birth_overlay_def] >>
  simp[ptr_birth_overlay_idempotent]
QED

Theorem ptr_gap_ownership_scan:
  !n a h tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  a.po_state.vs_inst_idx + n < LENGTH bb.bb_instructions /\
  (!q. a.po_state.vs_inst_idx <= q /\ q < a.po_state.vs_inst_idx + n ==>
    (EL q bb.bb_instructions).inst_opcode = NOP) ==>
  ?delta. LENGTH delta = n /\
    ptr_source_ownership vs0 C (h ++ delta) (ptr_gap_scan bb n a)
      tokens registry births PT (ptr_gap_tag_scan bb n a PT TG) saved
Proof
  Induct
  >- (rpt strip_tac >> qexists_tac `[]` >>
      simp[ptr_gap_scan_def, ptr_gap_tag_scan_def]) >>
  rpt gen_tac >> strip_tac >>
  `a.po_inst.inst_opcode = NOP` by
    (first_x_assum (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a (ptr_gap_next bb a)
     PT TG saved PT (step_prov PT TG a.po_inst a.po_state) saved` by
    (irule ptr_gap_tagged_next >> simp[]) >>
  `ptr_source_ownership vs0 C (h ++ [ptr_gap_next bb a]) (ptr_gap_next bb a)
     tokens registry
     births PT (step_prov PT TG a.po_inst a.po_state) saved` by
    (drule_all (cj 2 ptr_source_ownership_rules) >>
     drule ptr_ownership_overlay_fixed >>
     simp[ptr_activation_tokens_def, ptr_activation_registry_def, ptr_gap_next_fields]) >>
  first_x_assum (qspec_then `ptr_gap_next bb a` mp_tac) >>
  disch_then drule >>
  simp[ptr_gap_next_fields, ADD_CLAUSES] >>
  strip_tac >> qexists_tac `ptr_gap_next bb a :: delta` >>
  simp[ptr_gap_scan_def, ptr_gap_tag_scan_def] >>
  qpat_x_assum `ptr_source_ownership _ _ ((h ++ _) ++ delta) _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]
QED

Theorem ptr_gap_ownership_interval:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  a.po_state.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions /\
  (!q. a.po_state.vs_inst_idx <= q /\ q < k ==>
    (EL q bb.bb_instructions).inst_opcode = NOP) ==>
  ?delta b. LENGTH delta = k - a.po_state.vs_inst_idx /\
    b = ptr_gap_scan bb (k - a.po_state.vs_inst_idx) a /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births PT
      (ptr_gap_tag_scan bb (k - a.po_state.vs_inst_idx) a PT TG) saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL k bb.bb_instructions /\
    b.po_state = (a.po_state with vs_inst_idx := k)
Proof
  strip_tac >>
  `a.po_state.vs_inst_idx + (k - a.po_state.vs_inst_idx) = k` by decide_tac >>
  `?delta. LENGTH delta = k - a.po_state.vs_inst_idx /\
    ptr_source_ownership vs0 C (h ++ delta)
      (ptr_gap_scan bb (k - a.po_state.vs_inst_idx) a)
      tokens registry births PT
      (ptr_gap_tag_scan bb (k - a.po_state.vs_inst_idx) a PT TG) saved` by
    (irule ptr_gap_ownership_scan >> simp[]) >>
  qexistsl_tac [`delta`,`ptr_gap_scan bb (k - a.po_state.vs_inst_idx) a`] >>
  simp[ptr_gap_scan_fields] >>
  Cases_on `k = a.po_state.vs_inst_idx`
  >- simp[ptr_gap_scan_def] >>
  `0 < k - a.po_state.vs_inst_idx` by decide_tac >>
  metis_tac[ptr_gap_scan_fields]
QED

Theorem ptr_gap_ownership_history:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ptr_chrono_history vs0 C h a
Proof
  metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations,
    ptr_source_activations_sound]
QED

Theorem ptr_gap_ownership_aligned:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP positions (Allocation i.inst_id) = SOME p) /\
  ptr_ledger_block_alignment positions bb.bb_instructions tgt indices /\
  j < LENGTH indices /\ a.po_state.vs_inst_idx <= EL j indices /\
  (j = 0 \/ EL (j-1) indices < a.po_state.vs_inst_idx) ==>
  ?delta b. LENGTH delta = EL j indices - a.po_state.vs_inst_idx /\
    b = ptr_gap_scan bb (EL j indices - a.po_state.vs_inst_idx) a /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births PT
      (ptr_gap_tag_scan bb (EL j indices - a.po_state.vs_inst_idx) a PT TG) saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL j indices) bb.bb_instructions /\
    b.po_state = (a.po_state with vs_inst_idx := EL j indices)
Proof
  strip_tac >>
  `EL j indices < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> metis_tac[]) >>
  irule ptr_gap_ownership_interval >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule ptr_ledger_source_gap >>
  qexistsl_tac [`a.po_fn`,`indices`,`j`,`positions`,`tgt`] >>
  asm_rewrite_tac[] >> decide_tac
QED
