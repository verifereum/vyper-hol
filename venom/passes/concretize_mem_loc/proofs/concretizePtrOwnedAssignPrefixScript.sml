Theory concretizePtrOwnedAssignPrefix
Ancestors concretizePtrAffineTransport concretizePtrValueTransport
  concretizePtrDeletedGapHistory concretizePtrDeletedGaps
  concretizePtrLedgerAlignment concretizePtrSourceOwnership
  concretizePtrChronologicalHistory concretizePtrLedgerProbe
  concretizePtrActivationChronology concretizePtrActivationBirths concretizeMemLocDefs
  o1PassContract venomWf ptrDiscipline venomExecSemantics venomState
  venomInst codegenRel contextCodegenRel list arithmetic finite_map pred_set

Theorem ptr_assign_prefix_fn_wf:
  o1_ctx_shape C /\ MEM fn C.ctx_functions ==> fn_inst_wf fn
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_assign_prefix_nop_outputs:
  fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = NOP ==>
  inst.inst_outputs = []
Proof
  strip_tac >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  gvs[inst_wf_def]
QED

Theorem ptr_assign_prefix_nop_ghosts:
  inst.inst_opcode = NOP /\ inst.inst_outputs = [] ==>
  step_prov PT TG inst s = TG /\ step_taint inst s s tn = tn
Proof
  strip_tac >>
  `new_site_bytes s s = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `written_taint tn inst s = {}` by
    (simp[written_taint_def] >> Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
     Cases_on `t` >> simp[]) >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    set_var_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, taint_component_equality, DRESTRICT_UNIV,
    step_writes_def, source_memory_write_ranges_def, range_bytes_def]
QED

Theorem ptr_assign_prefix_gap_ghosts:
  !n a. fn_inst_wf a.po_fn /\ MEM bb a.po_fn.fn_blocks /\
    a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
    a.po_state.vs_inst_idx + n < LENGTH bb.bb_instructions /\
    (!q. a.po_state.vs_inst_idx <= q /\ q < a.po_state.vs_inst_idx + n ==>
      (EL q bb.bb_instructions).inst_opcode = NOP) ==>
    ptr_gap_tag_scan bb n a PT TG = TG /\
    (ptr_gap_scan bb n a).po_prov = a.po_prov /\
    (ptr_gap_scan bb n a).po_taint = a.po_taint
Proof
  Induct
  >- simp[ptr_gap_tag_scan_def, ptr_gap_scan_def] >>
  rpt gen_tac >> strip_tac >>
  `a.po_inst.inst_opcode = NOP` by
    (first_x_assum (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `a.po_inst.inst_outputs = []` by
    (irule ptr_assign_prefix_nop_outputs >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> irule EL_MEM >> decide_tac) >>
  `step_prov PT TG a.po_inst a.po_state = TG /\
   (ptr_gap_next bb a).po_prov = a.po_prov /\
   (ptr_gap_next bb a).po_taint = a.po_taint` by
    simp[ptr_gap_next_def, ptr_observe_def, ptr_assign_prefix_nop_ghosts] >>
  first_x_assum (qspec_then `ptr_gap_next bb a` mp_tac) >>
  simp[ptr_gap_next_fields, ADD_CLAUSES] >>
  simp[ptr_gap_scan_def, ptr_gap_tag_scan_def]
QED

Theorem ptr_assign_prefix_transport_cursor:
  ptr_vars_transport births positions TG tn s t ==>
  ptr_vars_transport births positions TG tn
    (s with vs_inst_idx := k) (t with vs_inst_idx := l)
Proof
  simp[ptr_vars_transport_def, lookup_var_def]
QED

Theorem ptr_assign_prefix_gap_transport:
  fn_inst_wf a.po_fn /\ MEM bb a.po_fn.fn_blocks /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  a.po_state.vs_inst_idx + n < LENGTH bb.bb_instructions /\
  (!q. a.po_state.vs_inst_idx <= q /\ q < a.po_state.vs_inst_idx + n ==>
    (EL q bb.bb_instructions).inst_opcode = NOP) /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t ==>
  ptr_vars_transport births positions (ptr_gap_tag_scan bb n a PT TG)
    (ptr_gap_scan bb n a).po_taint (ptr_gap_scan bb n a).po_state t
Proof
  strip_tac >> drule_all ptr_assign_prefix_gap_ghosts >> strip_tac >>
  simp[ptr_gap_scan_fields, ptr_vars_transport_def, lookup_var_def] >>
  gvs[ptr_vars_transport_def, lookup_var_def]
QED

(* This is a target-only operational segment: no source witnesses occur here. *)
Definition ptr_assign_target_segment_def:
  (ptr_assign_target_segment C bb 0 t u <=> u = t) /\
  (ptr_assign_target_segment C bb (SUC n) t u <=>
    ?post. step_inst 0 C (EL t.vs_inst_idx bb.bb_instructions) t = OK post /\
      ptr_assign_target_segment C bb n
        (post with vs_inst_idx := SUC t.vs_inst_idx) u)
End

Theorem ptr_assign_prefix_fields:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK post ==>
  post.vs_allocas = s.vs_allocas /\ post.vs_labels = s.vs_labels /\
  post.vs_current_bb = s.vs_current_bb /\ post.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> gvs[Once run_defs, step_inst_base_def, AllCaseEqs(), update_var_def]
QED

Theorem ptr_assign_prefix_attach:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  active_inst a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_opcode = ASSIGN /\ a.po_inst.inst_operands = [op] /\
  a.po_inst.inst_outputs = [out] /\
  step_inst 0 C a.po_inst a.po_state = OK post /\
  active_inst a.po_fn inst' (post with vs_inst_idx := SUC a.po_state.vs_inst_idx) ==>
  ptr_source_ownership vs0 C (h ++ [ptr_ledger_next a inst' post])
    (ptr_ledger_next a inst' post) tokens registry births PT
    (step_prov PT TG a.po_inst post) saved
Proof
  strip_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a (ptr_ledger_next a inst' post)
     PT TG saved PT (step_prov PT TG a.po_inst post) saved` by
    (simp[ptr_ledger_next_def] >>
     `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
       a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >>
     simp[ptr_tagged_step_def] >> metis_tac[]) >>
  drule_all (cj 2 ptr_source_ownership_rules) >>
  drule ptr_ownership_overlay_fixed >>
  drule_all ptr_assign_prefix_fields >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def,
    ptr_ledger_next_def, ptr_observe_def]
QED

Theorem ptr_assign_prefix_gap_aligned:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  fn_inst_wf a.po_fn /\ MEM bb a.po_fn.fn_blocks /\
  bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP layout (Allocation i.inst_id) = SOME p) /\
  ptr_ledger_block_alignment layout bb.bb_instructions tgt indices /\
  j < LENGTH indices /\ a.po_state.vs_inst_idx <= EL j indices /\
  (j = 0 \/ EL (j-1) indices < a.po_state.vs_inst_idx) /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t ==>
  ?delta b. LENGTH delta = EL j indices - a.po_state.vs_inst_idx /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births PT TG saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL j indices) bb.bb_instructions /\
    b.po_state = (a.po_state with vs_inst_idx := EL j indices) /\
    ptr_vars_transport births positions TG b.po_taint b.po_state t
Proof
  strip_tac >>
  `EL j indices < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> metis_tac[]) >>
  `!q. a.po_state.vs_inst_idx <= q /\ q < EL j indices ==>
    (EL q bb.bb_instructions).inst_opcode = NOP` by
    (rpt strip_tac >> irule ptr_ledger_source_gap >>
     qexistsl_tac [`a.po_fn`,`indices`,`j`,`layout`,`tgt`] >>
     simp[] >> decide_tac) >>
  `a.po_state.vs_inst_idx + (EL j indices - a.po_state.vs_inst_idx) = EL j indices`
    by decide_tac >>
  `ptr_gap_tag_scan bb (EL j indices - a.po_state.vs_inst_idx) a PT TG = TG` by
    (irule (cj 1 ptr_assign_prefix_gap_ghosts) >> gvs[]) >>
  `(ptr_gap_scan bb (EL j indices - a.po_state.vs_inst_idx) a).po_taint = a.po_taint`
    by (irule (cj 3 ptr_assign_prefix_gap_ghosts) >> gvs[]) >>
  drule_all ptr_gap_ownership_interval >> strip_tac >>
  qexistsl_tac [`delta`,`b`] >> gvs[] >>
  gvs[ptr_vars_transport_def, lookup_var_def]
QED

Theorem ptr_assign_prefix_back_next:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  MEM bb a.po_fn.fn_blocks /\ bb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  a.po_inst.inst_opcode = ASSIGN /\ a.po_inst.inst_operands = [op] /\
  a.po_inst.inst_outputs = [out] /\ step_inst 0 C' a.po_inst t = OK post ==>
  ?b TG'. ptr_source_ownership vs0 C (h ++ [b]) b tokens registry births PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL b.po_state.vs_inst_idx bb.bb_instructions /\
    b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    ptr_vars_transport births positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac) >>
  drule_all ptr_assign_transport_back_all >>
  disch_then (qspecl_then [`PT`,`C`] strip_assume_tac) >>
  `s'.vs_allocas = a.po_state.vs_allocas /\
   s'.vs_labels = a.po_state.vs_labels /\
   s'.vs_current_bb = a.po_state.vs_current_bb /\
   s'.vs_inst_idx = a.po_state.vs_inst_idx` by
    (irule ptr_assign_prefix_fields >> rpt (goal_assum (drule_at Any))) >>
  `post.vs_labels = t.vs_labels` by
    (irule (cj 2 ptr_assign_prefix_fields) >> rpt (goal_assum (drule_at Any))) >>
  `active_inst a.po_fn (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions)
    (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[]) >>
  qexistsl_tac [`ptr_ledger_next a
    (EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions) s'`,
    `step_prov PT TG a.po_inst s'`] >>
  conj_tac
  >- (irule ptr_assign_prefix_attach >> rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  simp[ptr_ledger_next_def, ptr_observe_def] >>
  irule ptr_assign_prefix_transport_cursor >> gvs[]
QED

Theorem ptr_assign_prefix_aligned_next:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  fn_inst_wf a.po_fn /\ MEM sb a.po_fn.fn_blocks /\
  sb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL (EL j indices) sb.bb_instructions /\
  a.po_state.vs_inst_idx = EL j indices /\ t.vs_inst_idx = j /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP layout (Allocation i.inst_id) = SOME p) /\
  ptr_ledger_block_alignment layout sb.bb_instructions tb.bb_instructions indices /\
  SUC j < LENGTH indices /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  a.po_inst.inst_opcode = ASSIGN /\ a.po_inst.inst_operands = [op] /\
  a.po_inst.inst_outputs = [out] /\
  step_inst 0 C' (EL j tb.bb_instructions) t = OK post ==>
  ?delta b TG'. LENGTH delta = EL (SUC j) indices - EL j indices /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    b.po_state.vs_inst_idx = EL (SUC j) indices /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    ptr_vars_transport births positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC j)
Proof
  strip_tac >>
  `EL j indices < EL (SUC j) indices` by
    (irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`layout`,`sb.bb_instructions`,`tb.bb_instructions`] >> simp[]) >>
  `LENGTH tb.bb_instructions = LENGTH indices /\
    EL (SUC j) indices < LENGTH sb.bb_instructions /\
    EL j tb.bb_instructions = a.po_inst` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_assum (qspec_then `SUC j` mp_tac) >>
     first_x_assum (qspec_then `j` mp_tac) >>
     simp[concretize_inst_with_positions_def] >> gvs[]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH sb.bb_instructions` by decide_tac >>
  `?b TG'. ptr_source_ownership vs0 C (h ++ [b]) b tokens registry births PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL b.po_state.vs_inst_idx sb.bb_instructions /\
    b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = post.vs_labels /\
    ptr_vars_transport births positions TG' b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ptr_assign_prefix_back_next >> rpt (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]) >>
  rename1 `ptr_source_ownership vs0 C (h ++ [b0]) b0 _ _ _ _ TG0 _` >>
  `?delta b. LENGTH delta = EL (SUC j) indices - b0.po_state.vs_inst_idx /\
    ptr_source_ownership vs0 C ((h ++ [b0]) ++ delta) b tokens registry births PT TG0 saved /\
    b.po_fn = b0.po_fn /\ b.po_stack = b0.po_stack /\ b.po_params = b0.po_params /\
    b.po_inst = EL (EL (SUC j) indices) sb.bb_instructions /\
    b.po_state = (b0.po_state with vs_inst_idx := EL (SUC j) indices) /\
    ptr_vars_transport births positions TG0 b.po_taint b.po_state
      (post with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule ptr_assign_prefix_gap_aligned >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >>
     qexistsl_tac [`layout`,`tb.bb_instructions`] >> simp[]) >>
  qexistsl_tac [`b0::delta`,`b`,`TG0`] >>
  qpat_x_assum `ptr_source_ownership _ _ ((h ++ [b0]) ++ delta) _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  simp[] >> strip_tac >> simp[] >>
  qpat_x_assum `ptr_vars_transport _ _ _ b.po_taint _ _` mp_tac >> simp[]
QED

Theorem ptr_assign_owned_prefix:
  !n a h TG j t u.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  fn_inst_wf a.po_fn /\ MEM sb a.po_fn.fn_blocks /\
  sb.bb_label = a.po_state.vs_current_bb /\
  a.po_inst = EL (EL j indices) sb.bb_instructions /\
  a.po_state.vs_inst_idx = EL j indices /\ t.vs_inst_idx = j /\
  (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP layout (Allocation i.inst_id) = SOME p) /\
  ptr_ledger_block_alignment layout sb.bb_instructions tb.bb_instructions indices /\
  j+n < LENGTH indices /\
  ptr_vars_transport births positions TG a.po_taint a.po_state t /\
  a.po_state.vs_labels = t.vs_labels /\
  (!k. j <= k /\ k < j+n ==>
    ?op out. (EL (EL k indices) sb.bb_instructions).inst_opcode = ASSIGN /\
      (EL (EL k indices) sb.bb_instructions).inst_operands = [op] /\
      (EL (EL k indices) sb.bb_instructions).inst_outputs = [out]) /\
  ptr_assign_target_segment C' tb n t u ==>
  ?delta b TG'. LENGTH delta = EL (j+n) indices - EL j indices /\
    ptr_source_ownership vs0 C (h ++ delta) b tokens registry births PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_inst = EL (EL (j+n) indices) sb.bb_instructions /\
    b.po_state.vs_inst_idx = EL (j+n) indices /\ u.vs_inst_idx = j+n /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_labels = u.vs_labels /\
    ptr_vars_transport births positions TG' b.po_taint b.po_state u
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`[]`,`a`,`TG`] >>
      gvs[ptr_assign_target_segment_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_assign_target_segment _ _ (SUC n) _ _` mp_tac >>
  simp[Once ptr_assign_target_segment_def] >> strip_tac >>
  `?op out. a.po_inst.inst_opcode = ASSIGN /\ a.po_inst.inst_operands = [op] /\
    a.po_inst.inst_outputs = [out]` by
    (qpat_x_assum `!k. _` (qspec_then `j` mp_tac) >> simp[]) >>
  `SUC j < LENGTH indices` by decide_tac >>
  drule_all ptr_assign_prefix_aligned_next >> strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >>
  disch_then drule >>
  disch_then (qspecl_then [`SUC j`,`post with vs_inst_idx := SUC j`,`u`] mp_tac) >>
  simp[ADD_CLAUSES] >>
  strip_tac >>
  `EL j indices < EL (SUC j) indices` by
    (irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`layout`,`sb.bb_instructions`,`tb.bb_instructions`] >> simp[]) >>
  `EL (SUC j) indices <= EL (SUC (j+n)) indices` by
    (Cases_on `n = 0` >- simp[] >>
     `SUC j < SUC (j+n) /\ SUC (j+n) < LENGTH indices` by decide_tac >>
     drule_all ptr_ledger_alignment_order >> decide_tac) >>
  qexistsl_tac [`delta ++ delta'`,`b'`,`TG''`] >>
  simp[APPEND_ASSOC] >> decide_tac
QED
