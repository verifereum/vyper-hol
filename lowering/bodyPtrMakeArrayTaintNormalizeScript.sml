(* Pointwise normalization prevents duplicated allocation-map quantifiers. *)
Theory bodyPtrMakeArrayTaintNormalize
Ancestors ptrDiscipline allocationPtr finite_map pred_set

Theorem new_site_bytes_unchanged:
  !s s'. s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  new_site_bytes s s' = {}
Proof
  rpt strip_tac >> simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem mem_taint_membership:
  !tn inst s s' i.
  (i IN mem_taint tn inst s s' <=>
   ((i IN tn.t_mem \/ i IN new_site_bytes s s') /\
    ~(i IN range_bytes (step_writes inst s s'))) \/
   i IN written_taint tn inst s)
Proof
  simp[mem_taint_def]
QED
