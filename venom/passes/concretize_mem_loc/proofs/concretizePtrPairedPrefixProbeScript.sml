Theory concretizePtrPairedPrefixProbe
Ancestors
  concretizePtrPairedPrefix concretizePtrValueTransport
  concretizePtrValueSelection concretizePtrAffineTransport
  concretizePtrOwnedAssignPrefix concretizePtrSharedFields
  concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory concretizePtrSourceOwnership
  concretizePtrLedgerAlignment makeSsaHelper o1PassContract unitTransformDefs
  contextCodegenRel ptrDiscipline venomExecSemantics lowerDloadDefs
  venomState list finite_map words

(* The raw total relation cannot represent arbitrary root parameters. *)
Theorem ptr_args_empty_tags_params_empty:
  ptr_args_transport births positions [] masks xs ys ==> xs = []
Proof
  simp[ptr_args_transport_def]
QED

Theorem ptr_paired_root_params:
  a.po_state.vs_params = at.po_state.vs_params ==>
  ptr_paired_params positions a at
    (tokens,registry,births,[],TG,saved,entries)
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_params_def]
QED

Theorem ptr_run_state_ok_params_unrestricted:
  o1_run_state_ok vs ==> o1_run_state_ok (vs with vs_params := params)
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def, code_layout_valid_def]
QED

Theorem ptr_paired_root_param_prov:
  inst.inst_opcode = PARAM ==> out_prov [] TG inst s' = NONE
Proof
  strip_tac >> simp[out_prov_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem ptr_paired_root_param_transport:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_params = t.vs_params /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH s.vs_params ==>
  ?s' t'. step_inst fuel C inst s = OK s' /\
    step_inst fuel Ct inst t = OK t' /\
    ptr_vars_transport births positions (step_prov [] TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `w2n idx < LENGTH t.vs_params` by metis_tac[] >>
  qexistsl_tac [`update_var out (EL (w2n idx) s.vs_params) s`,
               `update_var out (EL (w2n idx) t.vs_params) t`] >>
  drule_all ptr_param_step >> disch_then (fn th => simp[th]) >>
  simp[step_prov_def, out_prov_def] >>
  irule ptr_vars_transport_update >> rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def, eval_operand_def,
    ptr_value_transport_scalar_empty] >>
  qexists_tac `{}` >> simp[ptr_value_transport_scalar_empty]
QED

(* Administrative gaps leave runtime parameters unchanged, for either branch
   of the repaired parameter relation. *)
Theorem ptr_paired_gap_scan_params:
  ptr_paired_params positions a at
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_paired_params positions (ptr_gap_scan bb n a) at
    (tokens',registry',births,PT,TG',saved',entries')
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_params_def,
    ptr_gap_scan_fields]
QED

Theorem ptr_paired_cursor_normalize:
  ptr_paired_cursor local_positions a at /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb ==>
  ?n. ptr_paired_cursor local_positions (ptr_gap_scan bb n a) at /\
    (ptr_gap_scan bb n a).po_state.vs_inst_idx =
      a.po_state.vs_inst_idx + n /\
    !k. a.po_state.vs_inst_idx <= k /\
      k < a.po_state.vs_inst_idx + n ==>
      (EL k bb.bb_instructions).inst_opcode = NOP
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >>
  rpt strip_tac >>
  gvs[] >>
  qexists_tac `EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx` >>
  `a.po_state.vs_inst_idx +
    (EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx) =
    EL at.po_state.vs_inst_idx indices` by decide_tac >>
  simp[ptr_gap_scan_fields] >>
  qexists_tac `indices` >> simp[] >>
  Cases_on `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices`
  >- simp[ptr_gap_scan_def] >>
  `0 < EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx` by decide_tac >>
  simp[ptr_gap_scan_fields]
QED

Theorem ptr_paired_cursor_owned_scan:
  ptr_paired_cursor local_positions a at /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved ==>
  ?n delta. LENGTH delta = n /\
    ptr_source_ownership vs0 C (h ++ delta) (ptr_gap_scan bb n a)
      tokens registry births PT (ptr_gap_tag_scan bb n a PT TG) saved /\
    ptr_paired_cursor local_positions (ptr_gap_scan bb n a) at
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >>
  rpt strip_tac >> gvs[] >>
  `EL at.po_state.vs_inst_idx indices < LENGTH bb.bb_instructions` by
    (drule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_cursor >>
     strip_tac >> gvs[]) >>
  `?delta. LENGTH delta = EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx /\
    ptr_source_ownership vs0 C (h ++ delta)
      (ptr_gap_scan bb (EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx) a)
      tokens registry births PT
      (ptr_gap_tag_scan bb (EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx) a PT TG) saved` by
    (irule ptr_gap_ownership_scan >> simp[] >>
     `bb.bb_label = a.po_state.vs_current_bb` by
       metis_tac[lookup_block_label] >> simp[]) >>
  qexists_tac `delta` >>
  `a.po_state.vs_inst_idx + LENGTH delta = EL at.po_state.vs_inst_idx indices` by decide_tac >>
  simp[ptr_gap_scan_fields] >>
  qexists_tac `indices` >> simp[] >>
  Cases_on `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices`
  >- simp[ptr_gap_scan_def] >>
  `0 < EL at.po_state.vs_inst_idx indices - a.po_state.vs_inst_idx` by decide_tac >>
  simp[ptr_gap_scan_fields]
QED

Theorem ptr_paired_gap_scan_sample:
  fn_inst_wf a.po_fn /\ MEM bb a.po_fn.fn_blocks /\
  a.po_inst = EL a.po_state.vs_inst_idx bb.bb_instructions /\
  a.po_state.vs_inst_idx + n < LENGTH bb.bb_instructions /\
  (!q. a.po_state.vs_inst_idx <= q /\ q < a.po_state.vs_inst_idx + n ==>
    (EL q bb.bb_instructions).inst_opcode = NOP) /\
  ptr_paired_sample positions a at
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_paired_sample positions (ptr_gap_scan bb n a) at
    (tokens,registry,births,PT,ptr_gap_tag_scan bb n a PT TG,saved,entries)
Proof
  simp[ptr_paired_sample_def] >> strip_tac >> conj_tac
  >- (irule ptr_assign_prefix_gap_transport >> simp[]) >>
  gvs[ptr_gap_scan_fields, ptr_shared_fields_def]
QED
