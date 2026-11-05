Theory lowerDloadCopyCertificate
Ancestors
  lowerDloadVariableTransport lowerDloadAssignProducer lowerDloadPhiProducer
  lowerDloadOwnership ptrDiscipline venomState finite_map pred_set

(* The existing ASSIGN and parallel PHI certificates both conclude the first
   premise below. Their C1-C12 conclusions need not be duplicated to transport
   the separate frame floor and live allocation representation. lo <= f is
   unchanged; together with f <= next it supplies their lo <= next premise.
   This boundary establishes no annotated successor or block-label alignment. *)
Theorem ld_vars_floor_representation_transport:
  (t' with vs_vars := t.vs_vars) = t /\
  allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) ==>
  allocas_from f t' /\ f <= t'.vs_alloca_next /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t'.vs_allocas j = SOME(bt,sz))
Proof
  strip_tac >> dxrule ld_vars_restore_normalize >>
  disch_then SUBST_ALL_TAC >> simp[allocas_from_def] >>
  qpat_x_assum `allocas_from f t` mp_tac >> simp[allocas_from_def] >>
  strip_tac >> asm_rewrite_tac[]
QED
