Theory loadElimCaptureSteps
Ancestors
  loadElimCaptureInvariant loadElimTargetWrites loadElimDefs
  loadElimOccurrence loadElimKeyRead basePtrProofs list rich_list

Theorem le_latest_captures_step:
  le_latest_captures m ctx cfg result actions h t /\
  (!pa. MEM pa actions ==>
    lookup_var pa.pa_phi_out t' = lookup_var pa.pa_phi_out t) ==>
  le_latest_captures m ctx cfg result actions
    (h ++ [StepOcc bb n fuel u p]) t'
Proof
  strip_tac >>
  `le_latest_captures m ctx cfg result actions h t'` by
    (irule le_latest_captures_lookup_transport >> metis_tac[]) >>
  pop_assum mp_tac >> simp[le_latest_captures_def] >>
  rpt strip_tac >>
  qpat_x_assum `_ ++ [_] = _` mp_tac >>
  once_rewrite_tac[APPEND_EQ_APPEND] >>
  strip_tac >> gvs[APPEND_EQ_CONS] >>
  first_x_assum irule >> simp[] >>
  (conj_tac
   >- (qexistsl [`bb'`, `p'`, `pre`] >> simp[] >> metis_tac[]) >>
   qexistsl [`inst`, `lbl`] >> simp[])
QED

Theorem le_collected_step_capture_frame:
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  step_inst fuel run_ctx (load_elim_inst ctx actions ll inst) t = OK t' ==>
  !pa. MEM pa (collect_phi_actions m ctx cfg result fn) ==>
    lookup_var pa.pa_phi_out t' = lookup_var pa.pa_phi_out t
Proof
  rpt strip_tac >> irule step_inst_preserves_lookup >>
  goal_assum (drule_at Any) >>
  irule le_collected_transformed_output_fresh >> metis_tac[]
QED

Theorem le_latest_captures_transformed_step:
  le_latest_captures m ctx cfg result
    (collect_phi_actions m ctx cfg result fn) h t /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  step_inst fuel run_ctx
    (load_elim_inst ctx (collect_phi_actions m ctx cfg result fn) ll inst) t = OK t' ==>
  le_latest_captures m ctx cfg result
    (collect_phi_actions m ctx cfg result fn)
    (h ++ [StepOcc bb n source_fuel u p]) t'
Proof
  strip_tac >> irule le_latest_captures_step >>
  qexists `t` >> simp[] >>
  rpt strip_tac >> irule le_collected_step_capture_frame >> metis_tac[]
QED
