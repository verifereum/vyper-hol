Theory concretizeLayoutStageEntry
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutStagePairing
  frameActivationSeparation fmpAnalysisProps concretizeMemLocDefs

(* Initialize the canonical relation with the actual scheduled output,
   retaining the successful layout instead of replacing the function record. *)
Theorem layout_stage_entry_initial:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn.fn_eom = NONE /\ EVERY bb_well_formed fn.fn_blocks /\
  enters_block fn s p /\ s.vs_allocas = FEMPTY /\
  joint_trace vs0 C q0 es qs qend /\
  q0 = JointConfig [] [] FEMPTY entry_taint fn inst p [] FEMPTY hs h /\
  EL 0 ass = [([],FEMPTY)] ==>
  ?fn' positions.
    lookup_function name C'.ctx_functions = SOME fn' /\
    layout_driver_row C' fn fn' positions /\
    layout_canonical_run D lo vs0 C C' q0 es qs ass qend q0 0 fn s fn' s
Proof
  strip_tac >> drule_all layout_stage_row_produce >> strip_tac >>
  `fn.fn_name = name` by metis_tac[fmpAnalysisPropsTheory.lookup_function_name] >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `p.vs_allocas = FEMPTY` by metis_tac[enters_block_allocation_frame] >>
  qexistsl [`out`, `layout.cl_positions`] >> simp[] >>
  `layout_driver_row C' fn out layout.cl_positions` by
    (simp[layout_driver_row_def] >> metis_tac[]) >>
  simp[] >> irule layout_canonical_run_initial >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[layout_stage_row_def, apply_context_concretize_layout_def,
    apply_concretize_layout_def] >> metis_tac[]
QED

val _ = export_theory();
