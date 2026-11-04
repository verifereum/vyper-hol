Theory ctorAbiActualChildFrame
Ancestors
  ctorAbiActualSites ctorAbiActualMemory valueEncoding venomMemDefs
  abiEncoderRegisteredEffect pred_set arithmetic list finite_map

Theorem ctor_actual_child_preserves_value:
  abi_encoder_registered_effect (ctor_actual_sites fn child) [(c,k)] s t /\
  child SUBSET ids /\ ctor_actual_scratch fn ids D N t /\
  val_in_memory tv v p s.vs_memory /\ val_wf tv v /\
  D <= p /\ p + type_memory_size tv <= D+N /\
  regions_disjoint (p,type_memory_size tv) (c,k) ==>
  val_in_memory tv v p t.vs_memory
Proof
  strip_tac >> irule ctor_actual_registered_value >> simp[] >>
  qexistsl [`ctor_actual_sites fn child`, `[(c,k)]`, `s`] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >> drule_all ctor_actual_sites_scratch_contained >> simp[]) >>
  gvs[regions_disjoint_def] >> rpt strip_tac >> simp[] >> decide_tac
QED

Theorem ctor_actual_child_narrow_effect:
  abi_encoder_registered_effect (ctor_actual_sites fn child) [(c,k)] s t /\
  child SUBSET ids /\ d <= c /\ c+k <= d+n ==>
  abi_encoder_registered_effect (ctor_actual_sites fn ids) [(d,n)] s t
Proof
  strip_tac >> irule ctor_actual_child_effect >>
  qexistsl [`c`, `ctor_actual_sites fn child`, `k`] >> simp[ctor_actual_sites_mono]
QED
