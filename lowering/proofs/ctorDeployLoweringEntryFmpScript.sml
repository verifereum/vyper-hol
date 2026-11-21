(* A piece of deploy_ctor_entry_joint (ctorDeployLoweringEntry).
   fmp_room holds vacuously at every state of the constructor function: a
   supported program's raw deployment unit has no DALLOCA. *)
Theory ctorDeployLoweringEntryFmp
Ancestors
  ctorDeployLoweringDefs exprLoweringProps ctorDeployShape o1PipelineCorrect
  ptrDiscipline allocaFrontierRoom allocaFrontierBound entryDallocaCoverage
  venomMemDefs words list arithmetic

Theorem deploy_ctor_entry_fmp_room:
  !tops rpolicy runtime_bc dunit
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func s.
    supported_program tops /\ supported_program_deploy tops /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) ==>
    fmp_room dunit.cu_context func s
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule_all lower_vyper_deploy_unit_no_dalloca >>
  simp[fmp_room_def, ctx_has_dalloca_def, listTheory.EXISTS_MEM] >>
  metis_tac[]
QED

Theorem deploy_entry_frontier_fmp_room:
  alloca_frontier_inv_from k ctx func site s /\
  s.vs_fmp = s.vs_initial_fmp /\
  (ctx_has_dalloca ctx ==>
    k + unit_alloca_budget ctx <= w2n s.vs_initial_fmp /\
    w2n s.vs_initial_fmp < 2 ** 254) ==>
  fmp_room ctx func s
Proof
  strip_tac >>
  qpat_assum `alloca_frontier_inv_from _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [alloca_frontier_inv_from_def]) >>
  Cases_on `ctx_has_dalloca ctx`
  >- (fs[fmp_room_def, deploy_ctor_pending_alloca_eq, unit_alloca_frame_def,
         deploy_ctor_alloca_size_eq] >> decide_tac) >>
  irule context_without_dalloca_fmp_room >>
  conj_tac >- (fs[ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  metis_tac[venomInstTheory.lookup_function_MEM]
QED

Theorem deploy_entry_frontier_allocas_below_fmp:
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  k + unit_alloca_budget ctx <= w2n s.vs_initial_fmp /\
  w2n s.vs_initial_fmp <= w2n s.vs_fmp ==>
  allocas_below_fmp s /\
  s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp
Proof
  strip_tac >>
  qpat_assum `alloca_frontier_inv_from _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [alloca_frontier_inv_from_def]) >>
  fs[alloca_inv_def, alloca_next_valid_def, allocas_below_fmp_def,
     deploy_ctor_pending_alloca_eq] >>
  rpt strip_tac >> res_tac >> decide_tac
QED
