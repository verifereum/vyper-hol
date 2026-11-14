Theory guardPushProjections
Ancestors
  vfmAccountDeletion vfmAccountFrame vfmRunCall vfmStoragePredicates
  vfmExecutionProp vfmState vfmContext vfmTypes list arithmetic

Theorem step_push_static_output_not_code:
  wf_state s /\ step s = (INL u,e) /\
  LENGTH s.contexts < LENGTH e.contexts /\
  (FST (HD e.contexts)).msgParams.static ==>
  !x. (FST (HD e.contexts)).msgParams.outputTo <> Code x
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_reaches_proceed_call >> strip_tac >>
      drule_all call_prefix_contexts >> strip_tac >>
      drule_all proceed_call_inl_nonprecompile >> strip_tac >>
      drule_all proceed_call_nonprecompile_message >> strip_tac >>
      gvs[initial_context_def, initial_msg_params_def]) >>
  drule_all step_create_push_new_frame >> strip_tac >>
  qpat_x_assum `FST (HD e.contexts) = _`
    (mp_tac o AP_TERM ``\c:context. c.msgParams.static``) >>
  simp[initial_context_def, initial_msg_params_def]
QED

Theorem step_push_saved_to_delete:
  wf_state s /\ step s = (INL u,e) /\
  LENGTH s.contexts < LENGTH e.contexts ==>
  (SND (HD e.contexts)).toDelete = e.rollback.toDelete
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_deletion_projections >> strip_tac >>
      Cases_on `e.contexts` >> gvs[]) >>
  drule_all step_create_deletion_projections >> strip_tac >>
  Cases_on `e.contexts` >> gvs[]
QED
