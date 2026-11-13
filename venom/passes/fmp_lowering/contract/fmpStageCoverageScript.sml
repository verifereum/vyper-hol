(*
 * FmpLowering's lowered memory phase: every reachable instruction of the
 * lowered context C', run from the real state, accesses memory below the
 * static layout's end eom or at or above the real initial fmp.  Static
 * accesses of the raw input are unchanged; its dynamic ones lie in a live
 * DALLOCA site (row 3's access_ok) and are relocated to at or above the
 * real initial fmp; the inserted instructions access no memory.
 *
 * The proof is backward, by rule induction on the target's small-step
 * frame_reachable (concretize's ptr_raw_reachable_frame reaches it from
 * raw_reachable).  Every target state is covered (fmp_cov): it runs only
 * inserted instructions before a state related to a reachable source
 * point, or it sits in a revert forwarding's tail.  The step lemmas of
 * fmpStageOpSteps, fmpStageFmpSteps and fmpStageBlockSim move the source
 * point; fmpStageCoverBack gives them the terminating source step they
 * assume; fmpStageCoverInv states the invariant and gives each covered
 * state its memory fact.
 *
 * TOP-LEVEL:
 *   fmp_stage_coverage             - every target frame state is covered
 *   fmp_lowering_stage_lowered_mem
 *)
Theory fmpStageCoverage
Ancestors
  fmpStageCoverStep fmpStageCoverFrame fmpStageCoverInv fmpStageCoverCall fmpStageCoverBack fmpStageCoverMem fmpStageBlockSim fmpStageFmpSteps
  fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  concretizePtrCoverageStaticMemReachability ctxLookupAgreeHelpers
  concretizeStageLookup o1ContractSimplifyCfgSrcFrame fmpStageOpBaseActual
  fmpStepLayout fmpLowerDefs unitMemInv ptrDiscipline
  contextCodegenRel o1PassContract venomPassSchedule venomCompilerTypes
  passSimulationDefs venomExecSemantics venomState venomInst
  finite_map words list

Theorem fmp_stage_coverage:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom ==>
  !stk' PG' G' tn' fn' ti t.
    frame_reachable vs' C' stk' PG' G' tn' fn' ti t ==>
    fmp_cov D C C' vs vs' fmp eom stk' fn' t
Proof
  strip_tac >>
  `!vs0 ctx stk' PG' G' tn' fn' ti t.
     frame_reachable vs0 ctx stk' PG' G' tn' fn' ti t ==>
     vs0 = vs' /\ ctx = C' ==> fmp_cov D C C' vs vs' fmp eom stk' fn' t`
    suffices_by metis_tac[] >>
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- (irule fmp_cov_entry >> metis_tac[])
  >- (irule fmp_cov_next >> metis_tac[])
  >- (irule fmp_cov_block >> metis_tac[])
  >- (irule fmp_cov_call >> metis_tac[])
  >- (irule fmp_cov_ret >> metis_tac[])
QED

Theorem fmp_stage_lowered_entry_label[local]:
  fmp_stage_lowered infos ctx runner fn fn' ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  rw[fmp_stage_lowered_def] >>
  `fmp_lower_function ctx sp fn = SOME (fn',sp')` by
    simp[fmp_lower_function_def] >>
  drule fmp_lower_function_preserves_entry_label >> simp[]
QED

(* The lowering keeps the context entry, its function and its entry
   label. *)
Theorem fmp_stage_target_entry[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  C'.ctx_entry = SOME name /\
  ?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
        fn_entry_label fn' = SOME lbl
Proof
  strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
     (o1_walk_view rpolicy 3) C C'` by fs[fmp_stage_ctx_def] >>
  conj_tac >- fs[ctx_pass_stage_def] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  first_assum (irule_at Any) >>
  metis_tac[fmp_stage_actual_witness, fmp_stage_lowered_entry_label]
QED

Theorem fmp_lowering_stage_lowered_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
  o1_inv D 3 C (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
  fmp_variant_room (SOME fmp) C' vs' /\ max_live_eom C = SOME eom ==>
  mem_inv (lowered_mem_fact eom) C' vs'
Proof
  strip_tac >>
  `?vs. vs = vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>` by simp[] >>
  `fmp_stage_ctx rpolicy D C C' vs vs' fmp eom` by simp[fmp_stage_ctx_def] >>
  `mem_inv (static_mem_ok eom) C vs` by gvs[o1_inv_def, o1_static_inv_def] >>
  rewrite_tac[mem_inv_raw_reachable] >> conj_tac
  >- (fs[mem_inv_raw_reachable] >>
      drule_all fmp_stage_target_entry >> metis_tac[]) >>
  rpt strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  `active_inst fn inst s` by metis_tac[scfg_frame_reachable_active] >>
  `fmp_cov D C C' vs vs' fmp eom stk fn s` by metis_tac[fmp_stage_coverage] >>
  metis_tac[fmp_cov_mem]
QED
