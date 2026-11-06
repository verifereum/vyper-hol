Theory fnPlanLineageNativeTargets
Ancestors
  fnPlanLineagePhiClasses fnPlanLineageCallers fnPlanLineageLiveness
  fnPlanLineagePhiMaps livenessAnalysisProps

(* For a use-free prefix, entry membership is suffix membership minus all
   definitions in the prefix.  This deliberately states no list-count fact. *)
Theorem analyzed_use_free_prefix_partition:
  !n fn lbl bb v.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ n <= LENGTH bb.bb_instructions /\
  (!k. k < n ==> ~MEM v (inst_uses (EL k bb.bb_instructions))) ==>
  (MEM v (live_vars_at (liveness_analyze fn) lbl 0) <=>
   MEM v (live_vars_at (liveness_analyze fn) lbl n) /\
   !k. k < n ==> ~MEM v (inst_defs (EL k bb.bb_instructions)))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `n <= LENGTH bb.bb_instructions` by decide_tac >>
  `!k. k < n ==> ~MEM v (inst_uses (EL k bb.bb_instructions))` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `~MEM v (inst_uses (EL n bb.bb_instructions))` by
    (qpat_x_assum `!k. k < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`fn`, `lbl`, `bb`, `v`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  drule livenessAnalysisPropsTheory.live_vars_at_transfer >>
  disch_then (qspecl_then [`lbl`, `bb`, `n`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[livenessDefsTheory.liveness_transfer_def,
       livenessDefsTheory.live_update_def, listTheory.MEM_FILTER] >>
  metis_tac[DECIDE ``k < SUC n <=> k < n \/ k = n``]
QED

Theorem analyzed_unrenamed_phi_partition:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  phi_uses_disjoint (collect_phis bb.bb_instructions) /\
  EVERY (\phi. phi_well_formed phi.inst_operands)
    (collect_phis bb.bb_instructions) /\
  om = FST (build_phi_maps p (collect_phis bb.bb_instructions)) /\
  FLOOKUP om v = NONE ==>
  (MEM v (live_vars_at (liveness_analyze fn) lbl 0) <=>
   MEM v (live_vars_at (liveness_analyze fn) lbl
     (LENGTH (collect_phis bb.bb_instructions))) /\
   EVERY (\phi. ~MEM v (inst_defs phi)) (collect_phis bb.bb_instructions))
Proof
  strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  `!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_uses (EL k bb.bb_instructions))` by
    (gen_tac >> disch_tac >>
     `EL k bb.bb_instructions = EL k (collect_phis bb.bb_instructions)` by
       metis_tac[rich_listTheory.EL_APPEND1] >>
     `phi_well_formed (EL k (collect_phis bb.bb_instructions)).inst_operands` by
       (gvs[listTheory.EVERY_EL] >> first_x_assum irule >> simp[]) >>
     drule build_phi_maps_operand_class >>
     disch_then (qspecl_then [`v`, `p`, `k`] mp_tac) >>
     gvs[venomInstTheory.inst_uses_def,
         fnPlanLineageDemandSupportTheory.phi_well_formed_uses_pairs,
         listTheory.MEM_MAP] >>
     strip_tac >> gen_tac >> PairCases_on `y` >> simp[] >> metis_tac[]) >>
  drule analyzed_use_free_prefix_partition >>
  disch_then (qspecl_then [`LENGTH (collect_phis bb.bb_instructions)`,
                           `lbl`, `bb`, `v`] mp_tac) >>
  simp[] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp[] >>
  `(!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
       ~MEM v (inst_defs (EL k bb.bb_instructions))) <=>
    EVERY (\phi. ~MEM v (inst_defs phi)) (collect_phis bb.bb_instructions)` by
    (simp[listTheory.EVERY_EL] >>
     metis_tac[rich_listTheory.EL_APPEND1]) >>
  simp[]
QED

Theorem ready_join_target_counts:
  codegen_ready_fn fn /\ lookup_block succ fn.fn_blocks = SOME sb /\
  inst.inst_operands = [Label succ] /\
  join_target_ops (liveness_analyze fn) fn pred inst = SOME targets /\
  om = FST (build_phi_maps pred (collect_phis sb.bb_instructions)) ==>
  (FLOOKUP om v = NONE ==>
     LIST_ELEM_COUNT (Var v) targets =
       LIST_ELEM_COUNT v (live_vars_at (liveness_analyze fn) succ 0)) /\
  (!i. FLOOKUP om v = SOME i ==> LIST_ELEM_COUNT (Var v) targets <= 1)
Proof
  strip_tac >>
  `phi_uses_disjoint (collect_phis sb.bb_instructions)` by
    (irule ready_block_phi_uses_disjoint >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  gvs[stackPlanGenTheory.join_target_ops_def] >>
  simp[rich_listTheory.LIST_ELEM_COUNT_DEF, rich_listTheory.FILTER_MAP,
       combinTheory.o_DEF] >>
  pure_rewrite_tac[GSYM rich_listTheory.LIST_ELEM_COUNT_DEF] >>
  conj_tac
  >- (strip_tac >> irule input_vars_from_residual_count >> simp[]) >>
  rpt strip_tac >> irule input_vars_from_selected_count >> simp[] >>
  metis_tac[]
QED

(* Multiplicity checkpoint: ready_join_target_counts leaves exactly the
   NONE-map base counts to bound.  analyzed_unrenamed_phi_partition describes
   their membership (including PHI output kills), not their multiplicity.
   analyzed_terminal_jmp_target_coverage already supplies availability from
   predecessor live-out coverage, but one available resource does not bound
   repeated residual list entries.  The remaining native obligation is

     FLOOKUP om v = NONE ==> LIST_ELEM_COUNT v (live_vars_at ... succ 0) <= 1

   or a corresponding lower bound on actual available resources.  No such
   invariant is assumed here.  Ordinary ordered uses may repeat, as checked
   by repeated_operand_liveness_not_distinct.  The readiness audit does not
   supply the missing bound: codegen_ready_inst bounds the number of computed
   operands, not their multiplicities; var_use_count_block counts instructions
   containing Var v using MEM, not occurrences within an instruction.  Thus
   single_use_form does not itself exclude repeated operands in one ordinary
   instruction.  phi_block_ready excludes PHI inputs from post-prefix demand,
   but places no distinctness constraint on the remaining ordinary-use list.
   entry_boundary_resources supplies membership coverage and an UPPER resource
   bound of one for each live name, not a multiplicity-sensitive LOWER bound.
   Consequently these interfaces cannot yet discharge the residual obligation.
   Repetition within a PHI class is instead handled by the selected-count bound.
   This is an interface diagnosis, not a ready-function counterexample.
   Global analyzed-list distinctness, full native capacity, and the frozen
   theorem are not claimed.
*)

Theorem ready_unrenamed_phi_partition:
  codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  om = FST (build_phi_maps p (collect_phis bb.bb_instructions)) /\
  FLOOKUP om v = NONE ==>
  (MEM v (live_vars_at (liveness_analyze fn) lbl 0) <=>
   MEM v (live_vars_at (liveness_analyze fn) lbl
     (LENGTH (collect_phis bb.bb_instructions))) /\
   EVERY (\phi. ~MEM v (inst_defs phi)) (collect_phis bb.bb_instructions))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `wf_function fn /\ fn_inst_wf fn` by
    gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[ready_block_phi_uses_disjoint] >>
  `EVERY (\phi. inst_wf phi) (collect_phis bb.bb_instructions)` by
    (gvs[venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `EVERY (\phi. phi_well_formed phi.inst_operands)
    (collect_phis bb.bb_instructions)` suffices_by
    (strip_tac >> irule analyzed_unrenamed_phi_partition >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `p` >> gvs[]) >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  `phi.inst_opcode = PHI /\ inst_wf phi` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  metis_tac[cfgNormBaseTheory.inst_wf_phi_well_formed]
QED
