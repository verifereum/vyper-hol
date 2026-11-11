Theory fnPlanLineagePhiClasses
Ancestors
  fnPlanLineagePhiMaps fnPlanLineagePath fnPlanLineageLiveness

Theorem ready_block_phi_uses_disjoint:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
  phi_uses_disjoint (collect_phis bb.bb_instructions)
Proof
  simp[stackPlanGenTheory.codegen_ready_fn_def,
       stackPlanGenTheory.phi_operands_ready_def] >>
  strip_tac >>
  Cases_on `EVERY (\bb. NULL (collect_phis bb.bb_instructions)) fn.fn_blocks`
  >- (`NULL (collect_phis bb.bb_instructions)` by
        (qpat_x_assum `EVERY (\b. NULL _) _`
           (qspec_then `bb` mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >> simp[]) >>
      gvs[listTheory.NULL_EQ, stackPlanGenTheory.phi_uses_disjoint_def]) >>
  gvs[listTheory.EVERY_MEM, stackPlanGenTheory.phi_block_ready_def]
QED

Theorem reachable_native_phi_output_class_none:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM out_phi (collect_phis bb.bb_instructions) /\
  MEM v out_phi.inst_outputs ==>
  native_phi_class p (collect_phis bb.bb_instructions) (Var v) = NONE
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[ready_block_phi_uses_disjoint] >>
  Cases_on `native_phi_class p (collect_phis bb.bb_instructions) (Var v)`
  >- simp[] >>
  drule_all native_phi_class_use >> strip_tac >>
  `MEM (EL x (collect_phis bb.bb_instructions))
       (collect_phis bb.bb_instructions)` by
    metis_tac[listTheory.EL_MEM] >>
  drule_all reachable_phi_prefix_no_output_use_alias >> simp[]
QED

Theorem analyzed_native_phi_class_dead_range:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  native_phi_class p (collect_phis bb.bb_instructions) (Var v) = SOME i /\
  i < k /\ k <= LENGTH (collect_phis bb.bb_instructions) ==>
  ~MEM v (live_vars_at (liveness_analyze fn) lbl k)
Proof
  strip_tac >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    gvs[stackPlanGenTheory.phi_block_ready_def] >>
  drule_all native_phi_class_use >> strip_tac >>
  irule analyzed_phi_incoming_dead_after >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `i` >> simp[]
QED

Theorem analyzed_native_phi_class_dead_after:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  native_phi_class p (collect_phis bb.bb_instructions) (Var v) = SOME i ==>
  ~MEM v (live_vars_at (liveness_analyze fn) lbl (SUC i))
Proof
  strip_tac >> irule analyzed_native_phi_class_dead_range >>
  goal_assum (drule_at Any) >> simp[] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    gvs[stackPlanGenTheory.phi_block_ready_def] >>
  drule_all native_phi_class_use >> strip_tac >>
  qexistsl_tac [`i`, `p`] >> simp[]
QED
