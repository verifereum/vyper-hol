(* Successful source batches realize syntactic availability rows. *)
Theory makeSsaCurrentAvailabilityBoundary
Ancestors makeSsaCurrentFiniteAvailability makeSsaCurrentActualDefined
  makeSsaCurrentStaticDemandProbe venomExecSemantics venomState finite_map pred_set list

Theorem current_availability_phi_batch:
  lookup_block h fn.fn_blocks = SOME old /\
  eval_phis st old.bb_instructions = OK post /\
  (!v. MEM v (D (CurrentStaticCut p h 0 0)) ==> v IN FDOM st.vs_vars) /\
  current_availability_row fn D (CurrentStaticCut p h 0 0) d 0 ==>
  !v. MEM v (D d) ==> v IN FDOM post.vs_vars
Proof
  simp[current_availability_row_def, current_source_completed_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >>
  `MEM v (D (CurrentStaticCut p h 0 0)) \/
   MEM v (FLAT (MAP (\inst. inst.inst_outputs)
     (TAKE (phi_prefix_length old.bb_instructions) old.bb_instructions)))` by
    metis_tac[]
  >- (drule current_eval_phis_domain >> simp[SUBSET_DEF] >> metis_tac[]) >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[current_eval_phis_outputs]
QED
