Theory lowerDloadVariableTransport
Ancestors
  lowerDloadParamProducer lowerDloadOwnership lowerDloadPairedBoundary
  lowerDloadFrameCertificate lowerDloadAllocation lowerDloadRelocation
  venomExecProofs venomExecSemantics venomState finite_map list pred_set

(* eval_phis_only_updates_vs_vars already provides the parallel PHI
   restoration interface; do not duplicate its induction here. *)
Theorem ld_vars_restore_normalize:
  (s' with vs_vars := s.vs_vars) = s ==>
  s' = (s with vs_vars := s'.vs_vars)
Proof
  strip_tac >> pop_assum (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED

Theorem ld_frame_embedding_vars_transport:
  (s' with vs_vars := s.vs_vars) = s /\
  (t' with vs_vars := t.vs_vars) = t ==>
  (ld_frame_embedding E L H s' t' <=> ld_frame_embedding E L H s t)
Proof
  strip_tac >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >>
  simp[ld_frame_embedding_def]
QED

Theorem ld_alloc_account_vars_transport:
  (s' with vs_vars := s.vs_vars) = s /\
  (t' with vs_vars := t.vs_vars) = t ==>
  (ld_alloc_account keys d A s' t' <=> ld_alloc_account keys d A s t)
Proof
  strip_tac >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >>
  simp[ld_alloc_account_def]
QED

Theorem ld_byte_rel_vars_transport:
  (s' with vs_vars := s.vs_vars) = s /\
  (t' with vs_vars := t.vs_vars) = t ==>
  (ld_byte_rel R Ms Mt (\a. read_memory a 1 s') (\b. read_memory b 1 t') <=>
   ld_byte_rel R Ms Mt (\a. read_memory a 1 s) (\b. read_memory b 1 t))
Proof
  strip_tac >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >>
  simp[read_memory_def]
QED

Theorem ld_frame_bound_phis:
  ld_frame_bound n L AP AG ==>
  ld_frame_bound n L AP (ld_phis_prov prev AG ins)
Proof
  simp[ld_frame_bound_def, ld_selected_def] >>
  metis_tac[ld_phis_prov_selected]
QED

Theorem ld_live_phis:
  ld_live astk L AP (ld_phis_prov prev AG ins) site ==>
  ld_live astk L AP AG site
Proof
  simp[ld_live_def, ld_selected_def] >>
  metis_tac[ld_phis_prov_selected]
QED
