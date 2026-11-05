(* Producer compatibility is independent of backward read/read closure. *)
Theory makeSsaCurrentFiniteTransfer
Ancestors makeSsaCurrentFiniteTables makeSsaCurrentStaticDemandProbe
  makeSsaCurrentFiniteDemandProbe makeSsaCurrentFiniteHistory
  makeSsaCurrentHistoryProbe makeSsaCurrentPlacementCut
  makeSsaCurrentSimDefs makeSsaCurrentAllocation
  venomInst venomExecSemantics list rich_list

Definition current_table_pull_safe_def:
  current_table_pull_safe result =
    case result of
      SOME (CurrentStaticRead u,CurrentStaticRead v) => T
    | SOME (CurrentStaticProduced i,CurrentStaticProduced j) => (i = j)
    | _ => F
End

Definition current_table_safe_row_def:
  current_table_safe_row fn fn' table c d k =
    EVERY (\(e,x,y). current_table_pull_safe (current_table_pull fn fn' c k x y))
      (FILTER (\(e,x,y). e = d) table)
End

Theorem current_table_safe_row_sound:
  current_table_safe_row fn fn' table c d k /\ MEM (d,x,y) table ==>
  ?a b. current_static_back fn fn' c k x y a b /\
    ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
     (?i. a = CurrentStaticProduced i /\ b = CurrentStaticProduced i))
Proof
  simp[current_table_safe_row_def, EVERY_MEM, MEM_FILTER] >> strip_tac >>
  first_x_assum (qspec_then `(d,x,y)` mp_tac) >> simp[] >>
  Cases_on `current_table_pull fn fn' c k x y` >> simp[current_table_pull_safe_def] >>
  PairCases_on `x'` >> Cases_on `x'0` >> Cases_on `x'1` >>
  simp[current_table_pull_safe_def] >>
  metis_tac[current_table_pull_back]
QED

Theorem current_table_entry_sound:
  EVERY (\(e,x,y). x = y) (FILTER (\(e,x,y). e = c) table) ==>
  !x y. MEM (c,x,y) table ==> x = y
Proof
  simp[EVERY_MEM, MEM_FILTER] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `(c,x,y)` mp_tac) >> simp[]
QED

Theorem current_loop_table_entry:
  MEM (CurrentStaticCut "" "E" 0 0,x,y) current_loop_demand_table ==> x = y
Proof
  match_mp_tac current_table_entry_sound >> CONV_TAC (RAND_CONV EVAL) >> EVAL_TAC
QED

Theorem current_backedges_table_entry:
  MEM (CurrentStaticCut "" "E" 0 0,x,y) current_backedges_demand_table ==> x = y
Proof
  match_mp_tac current_table_entry_sound >> CONV_TAC (RAND_CONV EVAL) >> EVAL_TAC
QED

Theorem current_loop_demand_entry:
  current_finite_demand current_probe_loop (current_finite_target current_probe_loop)
    (current_finite_history current_probe_loop) (CurrentStaticCut "" "E" 0 0) x y ==>
  x = y
Proof
  metis_tac[current_loop_demand_contained, current_loop_table_entry]
QED

Theorem current_backedges_demand_entry:
  current_finite_demand history_probe_backedges (current_finite_target history_probe_backedges)
    (current_finite_history history_probe_backedges) (CurrentStaticCut "" "E" 0 0) x y ==>
  x = y
Proof
  metis_tac[current_backedges_demand_contained, current_backedges_table_entry]
QED


Theorem current_loop_safe_00:
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut "" "E" 0 0) (CurrentStaticCut "" "E" 0 0) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_loop_safe_01:
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut "" "E" 0 0) (CurrentStaticCut "" "E" 1 1) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_02:
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut "" "E" 1 1) (CurrentStaticCut "" "E" 2 2) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_03:
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut "" "E" 2 2) (CurrentStaticCut "E" "D" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_04:
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut "D" "X" 0 0) (CurrentStaticCut "D" "X" 0 0) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_loop_safe_05:
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut "D" "X" 0 0) (CurrentStaticCut "D" "X" 1 1) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_dispatch:
  MEM p ["E";"D"] ==>
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut p "D" 0 0) (CurrentStaticCut p "D" 1 1) 0
Proof
  simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED

Theorem current_loop_safe_cleanup:
  MEM p ["E";"D"] ==>
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut p "D" 1 1) (CurrentStaticCut p "D" 1 2) 1
Proof
  simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_body_0:
  MEM p ["E";"D"] ==>
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut p "D" 1 2) (CurrentStaticCut p "D" 2 3) 2
Proof
  simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_body_1:
  MEM p ["E";"D"] ==>
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut p "D" 2 3) (CurrentStaticCut p "D" 3 4) 2
Proof
  simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_transfer_D:
  MEM p ["E";"D"] ==>
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut p "D" 3 4) (CurrentStaticCut "D" "D" 0 0) 3
Proof
  simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_loop_safe_transfer_X:
  MEM p ["E";"D"] ==>
  current_table_safe_row current_probe_loop (current_finite_target current_probe_loop)
    current_loop_demand_table (CurrentStaticCut p "D" 3 4) (CurrentStaticCut "D" "X" 0 0) 3
Proof
  simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_finite_loop_source_blocks,
    current_finite_loop_target_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED

Theorem current_loop_safe_edges:
  EVERY (\(c,d,k). current_table_safe_row current_probe_loop
    (current_finite_target current_probe_loop) current_loop_demand_table c d k)
    current_loop_sparse_edges
Proof
  simp[current_loop_sparse_edges_def, current_loop_safe_00, current_loop_safe_01,
    current_loop_safe_02, current_loop_safe_03, current_loop_safe_04,
    current_loop_safe_05, current_loop_safe_dispatch, current_loop_safe_cleanup,
    current_loop_safe_body_0, current_loop_safe_body_1,
    current_loop_safe_transfer_D, current_loop_safe_transfer_X]
QED

Theorem current_table_safe_edges_sound:
  EVERY (\(c,d,k). current_table_safe_row fn fn' table c d k) edges /\
  (!c d k. current_finite_edge fn fn' c d k ==> MEM (c,d,k) edges) ==>
  !c d k x y. current_finite_edge fn fn' c d k /\ MEM (d,x,y) table ==>
  ?a b. current_static_back fn fn' c k x y a b /\
    ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
     (?i. a = CurrentStaticProduced i /\ b = CurrentStaticProduced i))
Proof
  simp[EVERY_MEM] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM (c,d,k) edges` by metis_tac[] >>
  qpat_x_assum `!e. MEM e edges ==> _` drule >> simp[] >>
  strip_tac >> drule_all current_table_safe_row_sound >> simp[]
QED

Theorem current_loop_finite_transfer:
  current_finite_edge current_probe_loop (current_finite_target current_probe_loop) c d k /\
  current_finite_demand current_probe_loop (current_finite_target current_probe_loop)
    (current_finite_history current_probe_loop) d x y ==>
  ?a b. current_static_back current_probe_loop (current_finite_target current_probe_loop)
    c k x y a b /\
    ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
     (?i. a = CurrentStaticProduced i /\ b = CurrentStaticProduced i))
Proof
  strip_tac >> drule current_loop_demand_contained >> strip_tac >>
  irule (Q.INST [`edges` |-> `current_loop_sparse_edges`,
    `table` |-> `current_loop_demand_table`] current_table_safe_edges_sound) >>
  simp[current_loop_safe_edges, current_loop_sparse_coverage] >> metis_tac[]
QED

Theorem current_backedges_safe_00:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "" "E" 0 0) (CurrentStaticCut "" "E" 0 0) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_01:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "" "E" 0 0) (CurrentStaticCut "" "E" 1 1) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_02:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "" "E" 1 1) (CurrentStaticCut "" "E" 2 2) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_03:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "" "E" 2 2) (CurrentStaticCut "" "E" 3 3) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_04:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "" "E" 3 3) (CurrentStaticCut "" "E" 4 4) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_05:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "" "E" 4 4) (CurrentStaticCut "E" "H" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_dispatch_E:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "E" "H" 0 0) (CurrentStaticCut "E" "H" 1 2) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED

Theorem current_backedges_safe_dispatch_D:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "D" "H" 0 0) (CurrentStaticCut "D" "H" 1 2) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_dispatch_S:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "S" "H" 0 0) (CurrentStaticCut "S" "H" 1 2) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_cleanup_E:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "E" "H" 1 2) (CurrentStaticCut "E" "H" 1 3) 1
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_cleanup_D:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "D" "H" 1 2) (CurrentStaticCut "D" "H" 1 3) 1
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_cleanup_S:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "S" "H" 1 2) (CurrentStaticCut "S" "H" 1 3) 1
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED

Theorem current_backedges_safe_body_0_E:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "E" "H" 1 3) (CurrentStaticCut "E" "H" 2 4) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_body_0_D:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "D" "H" 1 3) (CurrentStaticCut "D" "H" 2 4) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_body_0_S:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "S" "H" 1 3) (CurrentStaticCut "S" "H" 2 4) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_body_1_E:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "E" "H" 2 4) (CurrentStaticCut "E" "H" 3 5) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_body_1_D:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "D" "H" 2 4) (CurrentStaticCut "D" "H" 3 5) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_body_1_S:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "S" "H" 2 4) (CurrentStaticCut "S" "H" 3 5) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED

Theorem current_backedges_safe_transfer_D_E:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "E" "H" 3 5) (CurrentStaticCut "H" "D" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_transfer_D_D:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "D" "H" 3 5) (CurrentStaticCut "H" "D" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_transfer_D_S:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "S" "H" 3 5) (CurrentStaticCut "H" "D" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_transfer_S_E:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "E" "H" 3 5) (CurrentStaticCut "H" "S" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_transfer_S_D:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "D" "H" 3 5) (CurrentStaticCut "H" "S" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_transfer_S_S:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "S" "H" 3 5) (CurrentStaticCut "H" "S" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_06:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "D" 0 0) (CurrentStaticCut "H" "D" 0 0) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_07:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "D" 0 0) (CurrentStaticCut "H" "D" 1 1) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_08:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "D" 1 1) (CurrentStaticCut "H" "D" 2 2) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_09:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "D" 2 2) (CurrentStaticCut "D" "H" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_10:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "S" 0 0) (CurrentStaticCut "H" "S" 0 0) 0
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_11:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "S" 0 0) (CurrentStaticCut "H" "S" 1 1) 2
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED
Theorem current_backedges_safe_12:
  current_table_safe_row history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_demand_table (CurrentStaticCut "H" "S" 1 1) (CurrentStaticCut "S" "H" 0 0) 3
Proof
  rewrite_tac[current_table_safe_row_def] >> CONV_TAC (RAND_CONV EVAL) >>
  simp[current_table_pull_def, current_backedges_lookups,
    current_finite_backedges_source_blocks, history_probe_backedges_target_def,
    history_probe_bb_def, current_probe_inst_def] >> EVAL_TAC
QED

Theorem current_backedges_safe_edges:
  EVERY (\(c,d,k). current_table_safe_row history_probe_backedges
    (current_finite_target history_probe_backedges) current_backedges_demand_table c d k)
    current_backedges_sparse_edges
Proof
  simp[current_backedges_sparse_edges_def,
    current_backedges_safe_00, current_backedges_safe_01, current_backedges_safe_02,
    current_backedges_safe_03, current_backedges_safe_04, current_backedges_safe_05,
    current_backedges_safe_06, current_backedges_safe_07, current_backedges_safe_08,
    current_backedges_safe_09, current_backedges_safe_10, current_backedges_safe_11,
    current_backedges_safe_12,
    current_backedges_safe_dispatch_E, current_backedges_safe_dispatch_D,
    current_backedges_safe_dispatch_S,
    current_backedges_safe_cleanup_E, current_backedges_safe_cleanup_D,
    current_backedges_safe_cleanup_S,
    current_backedges_safe_body_0_E, current_backedges_safe_body_0_D,
    current_backedges_safe_body_0_S,
    current_backedges_safe_body_1_E, current_backedges_safe_body_1_D,
    current_backedges_safe_body_1_S,
    current_backedges_safe_transfer_D_E, current_backedges_safe_transfer_D_D,
    current_backedges_safe_transfer_D_S,
    current_backedges_safe_transfer_S_E, current_backedges_safe_transfer_S_D,
    current_backedges_safe_transfer_S_S]
QED

Theorem current_backedges_finite_transfer:
  current_finite_edge history_probe_backedges (current_finite_target history_probe_backedges) c d k /\
  current_finite_demand history_probe_backedges (current_finite_target history_probe_backedges)
    (current_finite_history history_probe_backedges) d x y ==>
  ?a b. current_static_back history_probe_backedges (current_finite_target history_probe_backedges)
    c k x y a b /\
    ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
     (?i. a = CurrentStaticProduced i /\ b = CurrentStaticProduced i))
Proof
  strip_tac >> drule current_backedges_demand_contained >> strip_tac >>
  irule (Q.INST [`edges` |-> `current_backedges_sparse_edges`,
    `table` |-> `current_backedges_demand_table`] current_table_safe_edges_sound) >>
  simp[current_backedges_safe_edges, current_backedges_sparse_coverage] >> metis_tac[]
QED
