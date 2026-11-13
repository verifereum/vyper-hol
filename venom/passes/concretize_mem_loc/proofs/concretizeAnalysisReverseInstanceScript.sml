Theory concretizeAnalysisReverseInstance
Ancestors
  concretizeAnalysisReverseCoverage concretizeAnalysisWriteSafety
  frameOriginHistory frameOriginReachable frameOriginCacheReach frameOriginUpdates
  concretizeMemLocDefs basePtrDefs cfgAnalysis memLocDefs
  concretizeAnalysisExclusiveWriters ptrDiscipline venomWf finite_map list

Theorem joint_origin_history_singleton_write_cached_site:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY fn_defs_reach_uses ctx.ctx_functions /\
  ctx_inst_ids_distinct ctx /\ all_reachable fn /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands /\
  allocation_exclusive P fn v /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (inst_write_op inst) = [Allocation killed] ==>
  ?site. FLOOKUP om v = SOME (OriginLocal killed,site) /\
         FLOOKUP G v = SOME site /\
         FLOOKUP s.vs_allocas killed = SOME site
Proof
  strip_tac >>
  `?aid site. FLOOKUP om v = SOME (OriginLocal aid,site)` by
    (drule joint_origin_history_ordinary_local_origin >> simp[] >>
     disch_then irule >> simp[] >> qexists `P` >> simp[]) >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule_all joint_origin_history_static_support >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by metis_tac[EVERY_MEM] >>
  `aid = killed` by (drule_all origin_frame_singleton_write_identity >> simp[]) >>
  gvs[] >> conj_tac
  >- (drule origin_frame_current_map >> strip_tac >>
      gvs[origin_erase_lookup]) >>
  drule_all origin_frame_current_cache >> simp[]
QED
