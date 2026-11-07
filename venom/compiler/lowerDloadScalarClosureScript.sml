Theory lowerDloadScalarClosure
Ancestors
  lowerDloadSharedState lowerDloadVariableTransport venomState

(* Scalar dispatch first applies ld_clean_scalar_certificate_backward for
   source success and geometry, then ld_scalar_taint_nonvar for mask equality.
   This boundary supplies its missing shared-state clause; ld_frame_data_def
   combines it with the certificate's ownership and definedness clauses.
   Normalize the same vars-only footprints to transport gas readings and
   exact non-current account/transient companions, without a second producer. *)
Theorem ld_shared_state_vars_transport:
  ld_shared_state tn un s t /\
  (s' with vs_vars := s.vs_vars) = s /\
  (t' with vs_vars := t.vs_vars) = t /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm /\ un'.t_stor = un.t_stor /\
  un'.t_trans = un.t_trans /\ un'.t_imm = un.t_imm ==>
  ld_shared_state tn' un' s' t'
Proof
  strip_tac >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  fs[ld_shared_state_def]
QED
