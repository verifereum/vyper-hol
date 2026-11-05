Theory concretizePtrPairedPrefixProbe
Ancestors
  concretizePtrPairedPrefix concretizePtrValueTransport
  concretizePtrValueSelection concretizePtrAffineTransport
  concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory o1PassContract unitTransformDefs
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
