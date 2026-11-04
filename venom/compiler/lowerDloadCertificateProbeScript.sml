Theory lowerDloadCertificateProbe
Ancestors
  lowerDloadStoreProducer lowerDloadFrameCertificate lowerDloadTargetGeometry
  lowerDloadPairedBoundary lowerDloadOperand lowerDloadOwnership
  lowerDloadAllocation ptrDiscipline venomExecSemantics finite_map pred_set

Theorem ld_owned_empty_initial:
  !V E tn s. ld_owned_vars V E FEMPTY FEMPTY tn tn s s
Proof
  simp[ld_owned_vars_def, ld_owned_value_def] >>
  rpt strip_tac >> gvs[ld_mask_word_identity]
QED

Theorem ld_certificate_initial_boundary:
  s.vs_allocas = FEMPTY /\ FINITE keys /\ lo <= s.vs_alloca_next ==>
  ld_frame_embedding FEMPTY FEMPTY FEMPTY s s /\
  ld_owned_vars V FEMPTY FEMPTY FEMPTY entry_taint entry_taint s s /\
  (!v:string. v IN V ==> (lookup_var v s = NONE <=> lookup_var v s = NONE)) /\
  ld_alloc_account keys 0 {} s s /\
  ld_frame_bound s.vs_alloca_next FEMPTY [] FEMPTY /\
  ld_stack_bound s.vs_alloca_next [] /\ lo <= s.vs_alloca_next
Proof
  strip_tac >> drule_all ld_geometry_initial_charge >>
  simp[ld_owned_empty_initial, ld_frame_embedding_def,
       ld_owned_selection_def, ld_erase_def]
QED
