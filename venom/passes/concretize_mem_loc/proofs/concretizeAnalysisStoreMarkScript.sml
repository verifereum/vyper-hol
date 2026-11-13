Theory concretizeAnalysisStoreMark
Ancestors concretizePtrStoreCoverage concretizeAnalysisWriteSafety
  concretizeMemLocDefs list finite_map

(* Store insertion and preservation are already exported by
   concretizePtrStoreCoverage. Only the consumer adapters belong here. *)
Theorem ml_mark_stores_live_write_at:
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  MEM a (find_base_allocas_opt bpr (inst_write_op (EL i bb.bb_instructions))) ==>
  ?addrs. FLOOKUP (ml_mark_stores_live bpr fn ls) a = SOME addrs /\
    MEM (bb.bb_label,i) addrs
Proof
  rpt strip_tac >> irule ptr_mark_stores_covers_write >>
  goal_assum (drule_at Any) >>
  qexists_tac `EL i bb.bb_instructions` >>
  simp[indexedListsTheory.MEM_MAPi] >> metis_tac[]
QED

Theorem write_base_marked_key:
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var u /\
  Allocation aid IN bp_bases bpr u ==>
  MEM (Allocation aid) (find_base_allocas_opt bpr (inst_write_op inst))
Proof
  simp[inst_write_op_def, find_base_allocas_opt_def,
       GSYM bp_bases_find_base_allocas]
QED
