Theory concretizePtrOwnedAssignPrefix
Ancestors concretizePtrAffineTransport concretizePtrValueTransport
  concretizePtrDeletedGapHistory
  concretizePtrLedgerAlignment concretizePtrSourceOwnership
  concretizePtrChronologicalHistory
  o1PassContract venomWf ptrDiscipline venomExecSemantics venomState
  venomInst codegenRel list arithmetic finite_map pred_set

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
