Theory concretizeAnalysisWriteSafety
Ancestors
  ptrDiscipline arithmetic list finite_map concretizeAnalysisScanCoverage
  concretizePtrReadCoverage concretizeAnalysisBoundary concretizeMemLocDefs
  basePtrDefs frameOriginReachable frameOriginUpdates venomWf pred_set

Theorem confined_full_interval_start:
  !b off sz:num. b <= off /\ off + sz <= b + sz ==> off = b
Proof
  decide_tac
QED

Theorem access_ok_full_write_start:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (b,sz) /\
  MEM (off,sz) (source_memory_write_ranges inst s) /\ sz <> 0 ==>
  off = b
Proof
  rpt strip_tac >> gvs[access_ok_def, op_prov_def] >>
  qpat_x_assum `!off' len. MEM (off',len) (source_memory_write_ranges inst s) /\ _ ==> _`
    (qspecl_then [`off`,`sz`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem access_ok_full_write_covers:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (b,sz) /\
  MEM (off,sz) (source_memory_write_ranges inst s) /\ sz <> 0 /\
  b <= x /\ x < b + sz ==>
  off <= x /\ x < off + sz
Proof
  metis_tac[access_ok_full_write_start]
QED



Theorem bp_bases_find_base_allocas:
  a IN bp_bases bp v <=> MEM a (find_base_allocas bp (Var v))
Proof
  `!xs. set (incr_ssort alloc_to xs) = set xs` by
    metis_tac[enumeralTheory.set_OWL_thm, enumeralTheory.OWL] >>
  `(!p. (case p of Ptr alloc off => alloc) = ptr_base p)` by
    (Cases >> simp[ptr_base_def]) >>
  fs[EXTENSION] >> simp[bp_bases_def, find_base_allocas_def, SF ETA_ss]
QED

Theorem origin_frame_singleton_write_identity:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  FLOOKUP om v = SOME (OriginLocal aid,site) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (inst_write_op inst) = [Allocation killed] ==>
  aid = killed
Proof
  rpt strip_tac >>
  drule_all origin_frame_current_production_coverage >>
  simp[bp_bases_find_base_allocas] >>
  gvs[inst_write_op_def, find_base_allocas_opt_def]
QED
