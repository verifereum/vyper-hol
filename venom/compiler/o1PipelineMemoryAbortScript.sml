(* S5 for the additive static memory-or-abort invariant. *)
Theory o1PipelineMemoryAbort
Ancestors
  o1StaticAbortDefs contextStaticAbortRel contextPlanLayoutProps
  stepWriteFootprintAbort unitMemInv staticAbortMemDefs staticAbortDefs
  contextRawReachable contextCodegenRel stackPlanGen venomCompilerTypes
  venomPipelineDriver venomExecSemantics venomState words list pair

Theorem static_abort_safe_range[local]:
  !eom ctx fn inst s off len.
  static_mem_ok_abort eom ctx fn inst s /\
  ~in_revert_forward fn s /\ ~in_static_abort_prefix fn s /\
  MEM (off,len) (inst_mem_ranges inst s) ==>
  len = 0 \/ off + len <= eom
Proof
  rw[static_mem_ok_abort_def, static_mem_ok_def, EVERY_MEM, FORALL_PROD] >>
  res_tac >> fs[]
QED

Theorem static_abort_reads_disjoint[local]:
  !eom ctx fn inst s cp.
  static_mem_ok_abort eom ctx fn inst s /\
  ~in_revert_forward fn s /\ ~in_static_abort_prefix fn s /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base) ==>
  source_memory_reads_disjoint cp inst s
Proof
  rw[source_memory_reads_disjoint_def, EVERY_MEM, FORALL_PROD] >>
  rename1 `MEM (off,len) (source_memory_read_ranges inst s)` >>
  `MEM (off,len) (inst_mem_ranges inst s)` by simp[inst_mem_ranges_def] >>
  drule_all static_abort_safe_range >> strip_tac >> simp[] >>
  disj2_tac >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem static_abort_writes_disjoint[local]:
  !eom ctx fn inst s cp.
  static_mem_ok_abort eom ctx fn inst s /\
  ~in_revert_forward fn s /\ ~in_static_abort_prefix fn s /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base) ==>
  context_source_memory_writes_disjoint cp inst s
Proof
  rw[context_source_memory_writes_disjoint_def, EVERY_MEM, FORALL_PROD] >>
  rename1 `MEM (off,len) (source_memory_write_ranges inst s)` >>
  `MEM (off,len) (inst_mem_ranges inst s)` by simp[inst_mem_ranges_def] >>
  drule_all static_abort_safe_range >> strip_tac >> simp[] >>
  disj2_tac >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem static_abort_spill_step_safe[local]:
  !ctx vs eom cp fn inst s fuel s'.
  step_write_footprint_abort ctx vs /\
  (!fn inst s. raw_reachable vs ctx fn inst s ==>
               static_mem_ok_abort eom ctx fn inst s) /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base) /\
  raw_reachable vs ctx fn inst s /\
  ~in_revert_forward fn s /\ ~in_static_abort_prefix fn s /\
  step_inst fuel ctx inst s = OK s' ==>
  context_spill_step_safe cp s s'
Proof
  rw[context_spill_step_safe_def, context_spill_byte_def] >>
  CCONTR_TAC >> fs[step_write_footprint_abort_def] >>
  first_x_assum (qspecl_then [`fn`,`inst`,`s`,`s'`,`fuel`,`i`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `MEM (off,len) (inst_mem_ranges inst2 s2)` by simp[inst_mem_ranges_def] >>
  `static_mem_ok_abort eom ctx fn2 inst2 s2` by res_tac >>
  drule_all static_abort_safe_range >> res_tac >> decide_tac
QED

Theorem o1_pipeline_memory_obligations_abort:
  !out cp vs.
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    o1_lowered_inv_abort out.po_unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp ==>
    ?Inv. codegen_memory_obligations_abort Inv out.po_unit.cu_context cp /\
          codegen_reachability_package Inv out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  fs[o1_lowered_inv_abort_def, mem_inv_raw_reachable] >> gvs[] >>
  qexists_tac `raw_reachable vs` >> conj_tac
  >- (rw[codegen_memory_obligations_abort_def] >>
      metis_tac[static_abort_reads_disjoint, static_abort_writes_disjoint,
                static_abort_spill_step_safe, step_write_footprint_abort_holds]) >>
  metis_tac[raw_reachable_package]
QED

