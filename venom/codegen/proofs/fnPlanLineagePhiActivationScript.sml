Theory fnPlanLineagePhiActivation
Ancestors
  fnPlanLineageEntryWitness fnPlanLineagePhiSlots fnPlanLineagePhiMaps
  fnPlanLineageLiveness livenessDefs finite_map stackPlanGen venomWf
  livenessTransferProofs venomExecProps

(* Activation is class-lived, independently of the edge being realized. *)
Theorem input_vars_from_activated_class:
  !insts pred i live v.
  phi_uses_disjoint (collect_phis insts) /\
  EVERY (\phi. ?w. MEM (pred,w) (phi_pairs phi.inst_operands)) (collect_phis insts) /\
  i < LENGTH (collect_phis insts) /\
  (?p w. MEM (p,w) (phi_pairs (EL i (collect_phis insts)).inst_operands) /\ MEM w live) /\
  FIND (\(l,w). l = pred) (phi_pairs (EL i (collect_phis insts)).inst_operands) = SOME (pred,v) ==>
  MEM v (input_vars_from pred insts live)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (INR i) (phi_slot_trace (FST (build_phi_maps pred (collect_phis insts))) live)` by
    (simp[phi_slot_trace_class_mem] >> metis_tac[]) >>
  `FLOOKUP (SND (build_phi_maps pred (collect_phis insts))) i = SOME v` by
    (drule build_phi_maps_matching_index >> simp[]) >>
  `~NULL (collect_phis insts)` by (Cases_on `collect_phis insts` >> gvs[]) >>
  `!w j. MEM w live /\ FLOOKUP (FST (build_phi_maps pred (collect_phis insts))) w = SOME j ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps pred (collect_phis insts))) j)` by
    (rpt strip_tac >> drule_all build_phi_maps_matching_total >> simp[]) >>
  `input_vars_from pred insts live =
    MAP (phi_slot_realize (SND (build_phi_maps pred (collect_phis insts))))
      (phi_slot_trace (FST (build_phi_maps pred (collect_phis insts))) live)` by
    (irule input_vars_from_slot_factor >> simp[] >> first_assum ACCEPT_TAC) >>
  gvs[] >> simp[listTheory.MEM_MAP] >>
  qexists_tac `INR i` >> simp[phi_slot_realize_def]
QED

Theorem reachable_phi_incoming_activated:
  !fn entry lbl bb i pred v.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  FIND (\(l,w). l = pred)
    (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands) = SOME (pred,v) ==>
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ wf_ssa fn /\ def_dominates_uses fn /\ phi_operands_ready fn` by
    gvs[codegen_ready_fn_def, wf_ssa_def] >>
  `MEM (EL i (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
    simp[listTheory.EL_MEM] >>
  `MEM (EL i (collect_phis bb.bb_instructions)) bb.bb_instructions /\
    (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (`~EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` by
       (simp[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_DEF] >> qexists_tac `bb` >> simp[] >>
        Cases_on `collect_phis bb.bb_instructions` >> gvs[]) >>
     gvs[phi_operands_ready_def, phi_block_ready_def, listTheory.EVERY_MEM] >>
     metis_tac[]) >>
  `?p w. MEM (p,w) (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands) /\
    MEM w (live_vars_at (liveness_analyze fn) lbl 0)` by
    (irule reachable_phi_live_entry_representative >> goal_assum (drule_at Any) >> simp[]) >>
  `fn_cfg_edge fn pred bb.bb_label` by
    (drule FIND_MEM >> strip_tac >>
     gvs[def_dominates_uses_def, phi_edge_uses_wf_def] >> metis_tac[]) >>
  irule input_vars_from_activated_class >> simp[] >>
  conj_tac >- (qexists_tac `i` >> simp[] >> metis_tac[]) >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  drule collect_phis_mem >> strip_tac >>
  gvs[def_dominates_uses_def, phi_edge_uses_wf_def] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem reachable_phi_incoming_live_out:
  !fn entry lbl bb i pred v pred_bb.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  FIND (\(l,w). l = pred)
    (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands) = SOME (pred,v) /\
  cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pred_bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))` by
    (irule reachable_phi_incoming_activated >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `i` >> simp[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all analyzed_live_out_edge_subset >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED
