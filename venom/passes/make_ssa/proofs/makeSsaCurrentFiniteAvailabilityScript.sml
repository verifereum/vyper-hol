(* Independent must-definition certificates; no runtime simulation assumed. *)
Theory makeSsaCurrentFiniteAvailability
Ancestors makeSsaCurrentFiniteTransfer makeSsaCurrentFiniteTables
  makeSsaCurrentFiniteDemandProbe makeSsaCurrentStaticDemandProbe
  makeSsaCurrentHistoryProbe makeSsaCurrentPlacementCut makeSsaCurrentSimDefs
  venomExecSemantics venomInst list

Definition current_source_completed_def:
  current_source_completed fn (CurrentStaticCut p h i j) kind =
    case lookup_block h fn.fn_blocks of NONE => [] | SOME old =>
      if kind = 0 then FLAT (MAP (\inst. inst.inst_outputs)
        (TAKE (phi_prefix_length old.bb_instructions) old.bb_instructions))
      else if kind = 2 then (EL i old.bb_instructions).inst_outputs else []
End

Definition current_availability_row_def:
  current_availability_row fn D c d k <=>
    EVERY (\v. MEM v (D c) \/ MEM v (current_source_completed fn c k)) (D d)
End

Definition current_loop_available_def:
  current_loop_available (CurrentStaticCut p h i j) =
    if h = "E" then (if i = 0 then [] else ["a"])
    else if h = "D" then ["a"] ++
      (if p = "D" \/ 2 <= i then ["b"] else []) ++
      (if 1 <= i then ["v"] else [])
    else if h = "X" then ["a";"b";"v"] else []
End

Definition current_backedges_available_def:
  current_backedges_available (CurrentStaticCut p h i j) =
    if h = "E" then TAKE i ["a";"b";"x"]
    else if h = "H" then ["a";"b";"x"] ++
      (if 1 <= i then ["v"] else []) ++ (if 2 <= i then ["z"] else [])
    else if h = "D" \/ h = "S" then ["a";"b";"x"] else []
End

Theorem current_availability_empty_entry:
  current_loop_available (CurrentStaticCut "" "E" 0 0) = [] /\
  current_backedges_available (CurrentStaticCut "" "E" 0 0) = []
Proof
  EVAL_TAC
QED

Theorem current_loop_availability_edges:
  EVERY (\(c,d,k). current_availability_row current_probe_loop
    current_loop_available c d k) current_loop_sparse_edges
Proof
  simp[current_loop_sparse_edges_def, current_availability_row_def,
    current_source_completed_def, current_loop_available_def,
    current_finite_loop_source_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED

Theorem current_backedges_availability_edges:
  EVERY (\(c,d,k). current_availability_row history_probe_backedges
    current_backedges_available c d k) current_backedges_sparse_edges
Proof
  simp[current_backedges_sparse_edges_def, current_availability_row_def,
    current_source_completed_def, current_backedges_available_def,
    current_finite_backedges_source_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def, phi_prefix_length_def] >> EVAL_TAC
QED

(* Only dispatch selectors and target-only cleanup seeds require this
   independent existence check. Ordinary paired reads may fail in the source. *)
Definition current_extra_read_cut_def:
  current_extra_read_cut fn fn' (CurrentStaticCut p h i j) <=>
    (i = 0 /\ j = 0) \/
    (?old out. lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h fn'.fn_blocks = SOME out /\
      i = phi_prefix_length old.bb_instructions /\
      phi_prefix_length out.bb_instructions <= j /\
      j < current_static_body_start old.bb_instructions out.bb_instructions)
End

Definition current_available_seed_table_def:
  current_available_seed_table fn fn' D table <=>
    EVERY (\(c,x,y). current_extra_read_cut fn fn' c ==>
      case x of Var v => MEM v (D c) | _ => T) table
End

Theorem current_available_seed_table_sound:
  current_available_seed_table fn fn' D table /\ MEM (c,Var v,y) table /\
  current_extra_read_cut fn fn' c ==> MEM v (D c)
Proof
  simp[current_available_seed_table_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(c,Var v,y)` mp_tac) >> simp[]
QED

Theorem current_loop_extra_reads_available:
  current_available_seed_table current_probe_loop (current_finite_target current_probe_loop)
    current_loop_available current_loop_seed_table
Proof
  simp[current_available_seed_table_def, current_loop_seed_table_def,
    current_extra_read_cut_def, current_loop_available_def,
    current_finite_loop_source_blocks, current_finite_loop_target_blocks,
    lookup_block_def, FIND_def, INDEX_FIND_def, history_probe_bb_def,
    current_probe_inst_def, phi_prefix_length_def, current_static_body_start_def] >> EVAL_TAC
QED

Theorem current_backedges_extra_reads_available:
  current_available_seed_table history_probe_backedges (current_finite_target history_probe_backedges)
    current_backedges_available current_backedges_seed_table
Proof
  (* This fixture even has defined ordinary seed reads; this is not
     imposed as a general requirement on source executions. *)
  `EVERY (\(c,x,y). case x of Var v => MEM v (current_backedges_available c)
      | _ => T) current_backedges_seed_table` by EVAL_TAC >>
  gvs[current_available_seed_table_def, EVERY_MEM] >>
  rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_loop_seed_availability:
  current_finite_seed current_probe_loop (current_finite_target current_probe_loop)
    (current_finite_history current_probe_loop) c (Var v) y /\
  current_extra_read_cut current_probe_loop (current_finite_target current_probe_loop) c ==>
  MEM v (current_loop_available c)
Proof
  metis_tac[current_loop_seed_covered, current_loop_extra_reads_available,
    current_available_seed_table_sound]
QED

Theorem current_backedges_seed_availability:
  current_finite_seed history_probe_backedges (current_finite_target history_probe_backedges)
    (current_finite_history history_probe_backedges) c (Var v) y /\
  current_extra_read_cut history_probe_backedges (current_finite_target history_probe_backedges) c ==>
  MEM v (current_backedges_available c)
Proof
  metis_tac[current_backedges_seed_covered, current_backedges_extra_reads_available,
    current_available_seed_table_sound]
QED

Theorem current_availability_edges_sound:
  EVERY (\(c,d,k). current_availability_row fn D c d k) edges /\
  (!c d k. current_finite_edge fn fn' c d k ==> MEM (c,d,k) edges) ==>
  !c d k v. current_finite_edge fn fn' c d k /\ MEM v (D d) ==>
    MEM v (D c) \/ MEM v (current_source_completed fn c k)
Proof
  simp[EVERY_MEM, current_availability_row_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM (c,d,k) edges` by metis_tac[] >>
  qpat_x_assum `!e. MEM e edges ==> _` drule >> simp[]
QED

Theorem current_loop_availability_transfer:
  current_finite_edge current_probe_loop (current_finite_target current_probe_loop) c d k /\
  MEM v (current_loop_available d) ==>
  MEM v (current_loop_available c) \/ MEM v (current_source_completed current_probe_loop c k)
Proof
  metis_tac[current_availability_edges_sound, current_loop_availability_edges,
    current_loop_sparse_coverage]
QED

Theorem current_backedges_availability_transfer:
  current_finite_edge history_probe_backedges (current_finite_target history_probe_backedges) c d k /\
  MEM v (current_backedges_available d) ==>
  MEM v (current_backedges_available c) \/ MEM v (current_source_completed history_probe_backedges c k)
Proof
  metis_tac[current_availability_edges_sound, current_backedges_availability_edges,
    current_backedges_sparse_coverage]
QED
