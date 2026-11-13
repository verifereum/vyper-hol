(* Allocation lower bounds use the actual frontier, not a decoder budget. *)
Theory decoderAllocationBoundsPtr
Ancestors ptrDiscipline venomMemProps venomExecSemantics venomState finite_map

(* Frontier monotonicity is already exec_alloca_alloca_next_mono in
   venomMemProps; reuse that theorem rather than exporting a duplicate. *)
Theorem exec_alloca_preserves_allocas_from:
  exec_alloca inst s alloc_size = OK t /\
  allocas_from lower s /\ lower <= s.vs_alloca_next ==>
  allocas_from lower t
Proof
  simp[exec_alloca_def, AllCaseEqs(), update_var_def, LET_THM] >>
  rpt strip_tac >> gvs[allocas_from_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED
