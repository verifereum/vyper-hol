Theory ctorDeployLoweringEntryCompleteRegisterBoundary
Ancestors
  ctorDeployLoweringEntryResourceBoundary ctorAbiActualSites ctorAbiActualFrame
  venomMemDefs venomState venomInst finite_map pred_set list arithmetic

Theorem deploy_ctor_actual_registered_memory_prefix:
  abi_encoder_registered_effect (ctor_actual_sites func ids) outs s t /\
  ctor_actual_scratch func ids 0 q t /\
  (!b n. MEM (b,n) outs ==> q <= b) ==>
  !a. a < q ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  rpt strip_tac >> irule deploy_ctor_registered_memory_exclusion >>
  qexistsl_tac [`ctor_actual_sites func ids`, `outs`] >>
  asm_simp_tac bool_ss [] >> reverse conj_tac
  >- metis_tac[LESS_LESS_EQ_TRANS] >>
  rpt strip_tac >>
  gvs[ctor_actual_sites_def, GSPECIFICATION] >>
  qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [ctor_actual_scratch_def] >>
  disch_then drule_all >> simp[regions_disjoint_def] >> decide_tac
QED
