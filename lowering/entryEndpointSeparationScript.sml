(* Completed entry uniqueness separates every earlier open block from closed blocks. *)
Theory entryEndpointSeparation
Ancestors
  entryStopObserverConstruction loweringShapeDefs list rich_list compileEnv fragExec

Theorem entry_endpoint_closed_open_separate:
  cs_extends mid entry_end /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) ==>
  !bb. MEM bb mid.cs_blocks ==> bb.bb_label <> mid.cs_current_bb
Proof
  strip_tac >> drule block_labels_cs_extends >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, all_blocks_def, MEM_MAP, MEM_REVERSE] >>
  metis_tac[]
QED

Theorem entry_stop_has_code_completed:
  fn_has_code first mid fn /\ cs_extends mid entry_end /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) ==>
  fn_has_code first mid
    (entry_stop_function mid.cs_current_bb (LENGTH mid.cs_current_insts) iid fn)
Proof
  strip_tac >> irule entry_stop_has_code >> simp[] >>
  drule entry_endpoint_closed_open_separate >> simp[] >>
  simp[emitted_blocks_def] >> rpt strip_tac >>
  drule MEM_TAKE >> metis_tac[]
QED
