Theory concretizeAnalysisWriteSafety
Ancestors venomWfProps
  ptrDiscipline arithmetic list finite_map concretizeAnalysisScanCoverage
  concretizePtrReadCoverage concretizeAnalysisBoundary concretizeMemLocDefs
  basePtrDefs frameOriginReachable frameOriginUpdates venomWf pred_set
  concretizeAnalysisSupport concretizePtrIncomingOrigins frameOriginCacheReach
  concretizePtrParamShape concretizePtrParamSupport contextCodegenRel venomInst
  removeUnusedSsaProofs

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

Theorem production_base_alloca_derived:
  MEM (Allocation aid)
    (find_base_allocas (bp_analyze_fuel fuel cfg fn) (Var v)) ==>
  v IN pointer_derived_vars fn (alloca_roots fn)
Proof
  strip_tac >>
  `bp_get_ptrs (bp_analyze_fuel fuel cfg fn) v <> []` by
    (strip_tac >>
     gvs[GSYM bp_bases_find_base_allocas, bp_bases_def]) >>
  `bp_supported (pointer_derived_vars fn (alloca_roots fn))
    (bp_analyze_fuel fuel cfg fn)` by
    simp[bp_analyze_fuel_def, bp_supported_alloca_production] >>
  gvs[bp_supported_def] >> metis_tac[]
QED

Theorem frame_reachable_active[local]:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac >> simp[]
QED

Theorem origin_frame_singleton_write_instance:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  FLOOKUP G v = SOME site /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (inst_write_op inst) = [Allocation killed] ==>
  FLOOKUP om v = SOME (OriginLocal killed,site) /\
  FLOOKUP s.vs_allocas killed = SOME site
Proof
  strip_tac >>
  `?tag. FLOOKUP om v = SOME (tag,site)` by metis_tac[origin_frame_current_lookup] >>
  `frame_reachable vs0 ctx stk PG G tn fn inst s` by metis_tac[origin_frame_erasure] >>
  `MEM fn ctx.ctx_functions` by metis_tac[ptr_frame_current_static] >>
  `fn_ptr_ok P fn` by fs[EVERY_MEM] >>
  `MEM inst (fn_insts fn)` by
    (drule frame_reachable_active >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  `v IN pointer_derived_vars fn (alloca_roots fn)` by
    (irule production_base_alloca_derived >>
     gvs[inst_write_op_def, find_base_allocas_opt_def] >> metis_tac[MEM]) >>
  Cases_on `tag`
  >- (rename1 `FLOOKUP om v = SOME (OriginLocal local_id,site)` >>
      `local_id = killed` by metis_tac[origin_frame_singleton_write_identity] >>
      metis_tac[origin_frame_current_cache])
  >- (drule_all origin_frame_current_incoming >>
      fs[fn_ptr_ok_def] >> metis_tac[]) >>
  metis_tac[origin_frame_current_not_dynamic]
QED

Theorem origin_frame_singleton_full_write:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  FLOOKUP G v = SOME (b,sz) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (inst_write_op inst) = [Allocation killed] /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,sz) (source_memory_write_ranges inst s) /\ sz <> 0 ==>
  FLOOKUP s.vs_allocas killed = SOME (off,sz)
Proof
  strip_tac >>
  `off = b` by metis_tac[access_ok_full_write_start] >>
  metis_tac[origin_frame_singleton_write_instance]
QED

Theorem origin_frame_o1_singleton_full_write:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  o1_ctx_shape ctx /\ EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\ EVERY ssa_form ctx.ctx_functions /\
  ~ctx_has_dalloca ctx /\ wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  FLOOKUP G v = SOME (b,sz) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (inst_write_op inst) = [Allocation killed] /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,sz) (source_memory_write_ranges inst s) /\ sz <> 0 ==>
  FLOOKUP s.vs_allocas killed = SOME (off,sz)
Proof
  strip_tac >> drule o1_ctx_shape_instructions_wf >> strip_tac >>
  irule origin_frame_singleton_full_write >> metis_tac[]
QED
