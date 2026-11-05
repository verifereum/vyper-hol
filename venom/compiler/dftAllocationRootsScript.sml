Theory dftAllocationRoots
Ancestors
  dftOccurrenceFreshness dftRunRel dftSsaPreserve dftWf
  dftOriginalScheduleRuntime venomInst list sorting option

Theorem dft_wf_function_ids:
  wf_function f ==> dft_fn_ids f
Proof
  simp[dft_fn_ids_def, EVERY_MEM] >>
  metis_tac[wf_fn_block_inst_ids_distinct]
QED

Theorem dft_fn_rel_allocation_ids:
  dft_fn_rel f g ==> dft_fn_ids f /\ dft_fn_ids g
Proof
  strip_tac >> `dft_fn_ids f` by
    metis_tac[dft_fn_rel_def, dft_wf_function_ids] >> simp[] >>
  qpat_x_assum `dft_fn_rel _ _` mp_tac >>
  simp[dft_fn_rel_def] >> strip_tac >>
  gvs[dft_fn_ids_def, EVERY_EL, LIST_REL_EL_EQN] >>
  metis_tac[dft_block_rel_ids_distinct]
QED

Theorem dft_original_function_allocation_ids:
  dft_original_function f g ==> dft_fn_ids f /\ dft_fn_ids g
Proof
  strip_tac >> `dft_fn_ids f` by
    metis_tac[dft_original_function_def, dft_wf_function_ids] >> simp[] >>
  qpat_x_assum `dft_original_function _ _` mp_tac >>
  simp[dft_original_function_def] >> strip_tac >>
  gvs[dft_fn_ids_def, EVERY_EL, LIST_REL_EL_EQN] >>
  metis_tac[dft_original_block_perm, PERM_MAP, ALL_DISTINCT_PERM, PERM_SYM]
QED

Theorem dft_context_ids_from_members:
  EVERY dft_fn_ids C.ctx_functions ==> dft_ctx_ids C
Proof
  simp[EVERY_MEM, dft_ctx_ids_def] >>
  metis_tac[lookup_function_MEM]
QED

Theorem dft_related_context_allocation_ids:
  LIST_REL R C.ctx_functions D.ctx_functions /\
  (!f g. R f g ==> dft_fn_ids f /\ dft_fn_ids g) ==>
  dft_ctx_ids C /\ dft_ctx_ids D
Proof
  strip_tac >>
  `EVERY dft_fn_ids C.ctx_functions /\ EVERY dft_fn_ids D.ctx_functions` by
    (gvs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  metis_tac[dft_context_ids_from_members]
QED

Theorem dft_fn_rel_context_allocation_ids:
  LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions ==>
  dft_ctx_ids C /\ dft_ctx_ids D
Proof
  strip_tac >> irule dft_related_context_allocation_ids >>
  metis_tac[dft_fn_rel_allocation_ids]
QED

Theorem dft_original_context_allocation_ids:
  dft_original_context C D ==> dft_ctx_ids C /\ dft_ctx_ids D
Proof
  simp[dft_original_context_def] >> strip_tac >>
  irule dft_related_context_allocation_ids >>
  metis_tac[dft_original_function_allocation_ids]
QED

Theorem dft_context_entry_valid:
  dft_ctx_ids C /\ C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME f ==>
  dft_occ_valid (dft_occ_init (DftOpen (DftEnter f 0 s) [] n))
Proof
  metis_tac[dft_ctx_ids_def, dft_occ_valid_init]
QED

Theorem dft_fn_rel_entry_roots:
  LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions /\
  D.ctx_entry = C.ctx_entry /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME f ==>
  ?g. lookup_function name D.ctx_functions = SOME g /\
    dft_fn_rel f g /\
    dft_occ_valid (dft_occ_init (DftOpen (DftEnter f 0 s) [] n)) /\
    dft_occ_valid (dft_occ_init (DftOpen (DftEnter g 0 t) [] m))
Proof
  strip_tac >> drule dft_fn_rel_lookup_function >>
  disch_then (qspec_then `name` mp_tac) >> simp[] >>
  Cases_on `lookup_function name D.ctx_functions` >> simp[] >>
  strip_tac >> drule dft_fn_rel_allocation_ids >>
  metis_tac[dft_occ_valid_init]
QED
