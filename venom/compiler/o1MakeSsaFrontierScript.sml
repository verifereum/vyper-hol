Theory o1MakeSsaFrontier
Ancestors
  unitShapeDefs finite_map dominatorDefs cfgDefs cfgHelpers list
  makeSsaDefs venomInst venomWf makeSsaCurrentFrontier makeSsaCurrentWfSsa makeSsaCurrentTraceCertificate

(* Weak frontier support: no definite assignment or all_reachable premise.
   Adapted from the proved makeSsaCurrentFrontier reference theory. *)
Theorem current_frontier_not_entry:
  wf_function fn /\ first_block_no_preds fn /\
  MEM n (fn_labels fn) /\
  ALOOKUP (current_frontier_map fn) n = SOME fs /\ MEM y fs ==>
  fn_entry_label fn <> SOME y
Proof
  strip_tac >> drule_all current_frontier_target_count >> strip_tac >>
  strip_tac >> drule_all current_entry_preds_empty >> strip_tac >> gvs[]
QED

Theorem phi_pairs_build_phi_inst_supply:
  !preds. phi_pairs (build_phi_inst_supply id var preds).inst_operands =
    MAP (\l. (l,var)) preds
Proof
  Induct >> gvs[build_phi_inst_supply_def, phi_pairs_def]
QED

Theorem build_phi_inst_supply_shape:
  !preds. 2 <= LENGTH preds /\ ALL_DISTINCT preds ==>
  inst_shape_ok (build_phi_inst_supply id var preds)
Proof
  simp[inst_shape_ok_def, phi_pairs_build_phi_inst_supply,
       build_phi_inst_supply_def, label_positions_ok_def, is_read0_opcode_def,
       MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem current_frontier_phi_shape:
  MEM n (fn_labels fn) /\ MEM y (fn_labels fn) /\
  ALOOKUP (current_frontier_map fn) n = SOME fs /\ MEM y fs ==>
  inst_shape_ok (build_phi_inst_supply id var
    (case ALOOKUP (current_pred_map fn) y of NONE => [] | SOME ps => ps))
Proof
  strip_tac >> drule_all current_frontier_target_count >> strip_tac >>
  simp[ALOOKUP_current_pred_map] >> irule build_phi_inst_supply_shape >>
  simp[cfg_analyze_preds_distinct]
QED

(* Predicate-parametric insertion boundary: consumers choose a block-local
   structural invariant, and prove closure only for actual frontier targets. *)
Theorem process_frontiers_supply_invariant:
  !fs s var pm li bbs rest hp bbs' rest' hp' s' P.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') /\ EVERY P bbs /\
    (!f id bb. MEM f fs /\ P bb ==>
      P (if bb.bb_label = f then
        insert_phi_at_block (build_phi_inst_supply id var
          (case ALOOKUP pm f of NONE => [] | SOME ps => ps)) bb
        else bb)) ==>
    EVERY P bbs'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> first_x_assum irule >> metis_tac[MEM]) >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> first_x_assum irule >> metis_tac[MEM]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  first_x_assum drule >> disch_then irule >> conj_tac
  >- metis_tac[MEM] >>
  simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`h`, `id`, `bb`] mp_tac) >> simp[] >>
  metis_tac[EVERY_MEM]
QED

Theorem insert_phis_for_var_supply_invariant:
  !s var df pm li bbs wl hp bbs' s' P.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') /\
    EVERY P bbs /\
    (!d fs f id bb. ALOOKUP df d = SOME fs /\ MEM f fs /\ P bb ==>
      P (if bb.bb_label = f then
        insert_phi_at_block (build_phi_inst_supply id var
          (case ALOOKUP pm f of NONE => [] | SOME ps => ps)) bb
        else bb)) ==>
    EVERY P bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  `EVERY P bbs''` by
    (drule process_frontiers_supply_invariant >> disch_then irule >>
     simp[] >> Cases_on `ALOOKUP dom_frontiers d` >> simp[] >>
     metis_tac[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem current_frontier_key:
  ALOOKUP (current_frontier_map fn) k = SOME fs ==> MEM k (fn_labels fn)
Proof
  simp[current_frontier_map_def] >> metis_tac[current_query_map_lookup_domain]
QED

Theorem insert_phis_for_var_supply_shape:
  insert_phis_for_var_supply s var (current_frontier_map fn)
    (current_pred_map fn) li bbs wl hp = (bbs',s') /\
  EVERY (\bb. MEM bb.bb_label (fn_labels fn) /\
    EVERY inst_shape_ok bb.bb_instructions) bbs ==>
  EVERY (\bb. MEM bb.bb_label (fn_labels fn) /\
    EVERY inst_shape_ok bb.bb_instructions) bbs'
Proof
  strip_tac >> drule insert_phis_for_var_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[makeSsaDefsTheory.insert_phi_at_block_def] >>
  irule current_frontier_phi_shape >> metis_tac[current_frontier_key]
QED

Theorem add_phi_nodes_supply_invariant:
  !defs s df pm li bbs bbs' s' P.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\ EVERY P bbs /\
    (!var d fs f id bb. ALOOKUP df d = SOME fs /\ MEM f fs /\ P bb ==>
      P (if bb.bb_label = f then
        insert_phi_at_block (build_phi_inst_supply id var
          (case ALOOKUP pm f of NONE => [] | SOME ps => ps)) bb
        else bb)) ==>
    EVERY P bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  first_x_assum drule >> disch_then irule >> conj_tac
  >- metis_tac[] >>
  drule insert_phis_for_var_supply_invariant >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Theorem add_phi_nodes_supply_shape:
  add_phi_nodes_supply s (current_frontier_map fn)
    (current_pred_map fn) li bbs defs = (bbs',s') /\
  EVERY (\bb. MEM bb.bb_label (fn_labels fn) /\
    EVERY inst_shape_ok bb.bb_instructions) bbs ==>
  EVERY (\bb. MEM bb.bb_label (fn_labels fn) /\
    EVERY inst_shape_ok bb.bb_instructions) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[makeSsaDefsTheory.insert_phi_at_block_def] >>
  irule current_frontier_phi_shape >> metis_tac[current_frontier_key]
QED

Theorem add_phi_nodes_supply_entry:
  wf_function fn /\ first_block_no_preds fn /\
  fn_entry_label fn = SOME entry /\
  add_phi_nodes_supply s (current_frontier_map fn) pm li bbs defs = (bbs',s') ==>
  EVERY (\bb. bb.bb_label = entry ==> MEM bb bbs) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >>
      `f <> entry` by
        (`MEM d (fn_labels fn)` by metis_tac[current_frontier_key] >>
         drule_all current_frontier_not_entry >> simp[]) >>
      IF_CASES_TAC >> gvs[makeSsaDefsTheory.insert_phi_at_block_def]) >>
  simp[EVERY_MEM]
QED

Theorem insert_phi_at_block_well_formed:
  bb_well_formed bb /\ phi.inst_opcode = PHI ==>
  bb_well_formed (insert_phi_at_block phi bb)
Proof
  simp[bb_well_formed_def, makeSsaDefsTheory.insert_phi_at_block_def] >>
  strip_tac >> simp[LAST_DEF] >> conj_tac
  >- (Cases >> simp[is_terminator_def] >> metis_tac[]) >>
  Cases >> Cases >> simp[] >> metis_tac[]
QED

Theorem add_phi_nodes_supply_well_formed:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  EVERY bb_well_formed bbs ==> EVERY bb_well_formed bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  irule insert_phi_at_block_well_formed >> simp[build_phi_inst_supply_def]
QED

Theorem add_phi_nodes_supply_provenance:
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    li fn.fn_blocks defs = (bbs',s') ==>
  EVERY (\bb. MEM bb.bb_label (fn_labels fn) /\
    EVERY (\i. MEM i (fn_insts fn) \/
      (i.inst_opcode = PHI /\ inst_shape_ok i)) bb.bb_instructions) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> conj_tac
  >- (simp[] >> rpt strip_tac >> IF_CASES_TAC >>
      gvs[makeSsaDefsTheory.insert_phi_at_block_def] >>
      disj2_tac >> conj_tac >- simp[build_phi_inst_supply_def] >>
      irule current_frontier_phi_shape >> metis_tac[current_frontier_key]) >>
  simp[EVERY_MEM, fn_labels_def, fn_insts_def, MEM_fn_insts_blocks_iff,
       MEM_MAP] >>
  metis_tac[]
QED
