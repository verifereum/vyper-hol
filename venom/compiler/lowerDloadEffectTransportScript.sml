Theory lowerDloadEffectTransport
Ancestors
  lowerDloadSharedState venomState

Theorem ld_memory_restore_normalize:
  (s' with vs_memory := s.vs_memory) = s ==>
  s' = (s with vs_memory := s'.vs_memory)
Proof
  strip_tac >> pop_assum (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED

(* Memory effects leave the three nonmemory shared-state masks unchanged.
   The two memories need not agree, either before or after the effect. *)
Theorem ld_shared_state_memory_transport:
  ld_shared_state tn un s t /\
  (s' with vs_memory := s.vs_memory) = s /\
  (t' with vs_memory := t.vs_memory) = t /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm /\ un'.t_stor = un.t_stor /\
  un'.t_trans = un.t_trans /\ un'.t_imm = un.t_imm ==>
  ld_shared_state tn' un' s' t'
Proof
  strip_tac >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  fs[ld_shared_state_def]
QED
