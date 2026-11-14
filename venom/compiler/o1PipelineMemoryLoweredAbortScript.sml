(* S5 with static-abort prefixes and dynamic memory above the initial FMP. *)
Theory o1PipelineMemoryLoweredAbort
Ancestors
  o1PassContract contextStaticAbortRel contextPlanLayoutProps
  stepWriteFootprintAbort unitMemInv staticAbortDefs ctxLookupAgree
  contextRawReachable contextCodegenRel stackPlanGen venomCompilerTypes
  venomPipelineDriver venomExecSemantics venomState words list pair

Theorem lowered_abort_spill_step_safe[local]:
  !ctx vs eom fmp cp fn inst s fuel s'.
  step_write_footprint_abort ctx vs /\
  (!fn inst s. raw_reachable vs ctx fn inst s ==>
    in_static_abort_prefix fn s \/ lowered_mem_ok eom fmp ctx fn inst s) /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base /\ r.sr_spill_end <= fmp) /\
  raw_reachable vs ctx fn inst s /\ ~in_revert_forward fn s /\
  ~in_static_abort_prefix fn s /\ step_inst fuel ctx inst s = OK s' ==>
  context_spill_step_safe cp s s'
Proof
  rw[context_spill_step_safe_def, context_spill_byte_def] >>
  CCONTR_TAC >> fs[step_write_footprint_abort_def] >>
  first_x_assum (qspecl_then [`fn`,`inst`,`s`,`s'`,`fuel`,`i`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `lowered_mem_ok eom fmp ctx fn2 inst2 s2` by metis_tac[] >>
  drule_all lowered_mem_ok_disjoint >> strip_tac >>
  fs[context_source_memory_writes_disjoint_def, EVERY_MEM, FORALL_PROD] >>
  res_tac >> fs[] >> res_tac >> decide_tac
QED

Theorem o1_pipeline_memory_obligations_lowered_abort:
  !out cp vs.
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
      mem_inv (\ctx fn inst s.
        in_static_abort_prefix fn s \/ lowered_mem_fact eom ctx fn inst s)
        out.po_unit.cu_context vs) /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp ==>
    ?Inv. codegen_memory_obligations_abort Inv out.po_unit.cu_context cp /\
          codegen_reachability_package Inv out.po_unit.cu_context vs
Proof
  rpt strip_tac >>
  rename1 `generate_context_plan _ = SOME plan` >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  fs[mem_inv_raw_reachable] >>
  gvs[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `!fn inst s. raw_reachable vs out.po_unit.cu_context fn inst s ==>
    in_static_abort_prefix fn s \/
    lowered_mem_ok plan.cp_max_static_eom plan.cp_initial_fmp
      out.po_unit.cu_context fn inst s` by
    (rpt strip_tac >> first_x_assum drule >>
     drule raw_reachable_initial_fmp >>
     simp[lowered_mem_fact_def, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  qexists_tac `raw_reachable vs` >> conj_tac
  >- (rw[codegen_memory_obligations_abort_def] >>
      metis_tac[lowered_mem_ok_disjoint, lowered_abort_spill_step_safe,
                step_write_footprint_abort_holds]) >>
  metis_tac[raw_reachable_package]
QED
