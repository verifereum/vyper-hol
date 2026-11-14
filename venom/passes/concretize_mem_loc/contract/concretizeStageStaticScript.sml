(*
 * ConcretizeMemLoc's stage contract, the memory part of row 3: every
 * access of the output is below its layout end.
 *
 * TOP-LEVEL:
 *   concretize_stage_static_mem
 *)
Theory concretizeStageStatic
Ancestors
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrUniversalExtension concretizePtrCoverageStaticMem
  concretizePtrFrameRetpcShape
  concretizePtrPairedPrefix concretizePtrCurrentObservation
  o1SafeUpto

(* Why it holds (intuition, not a prescribed proof).

   The pass replaces every ALLOCA with an ASSIGN of a literal position
   from the static layout, whose end is fn_eom <= max_live_eom C'; so C'
   has no ALLOCA, its static accesses are at those positions plus the
   in-site offsets ptr_discipline lo C allows, and its PARAM and
   pointer-compare uses are the input's.  Without DALLOCA, every access
   of C' is below the layout end. *)
Theorem concretize_stage_static_mem_ptr_upto[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\
  ptr_discipline_upto lo n C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  C.ctx_entry = SOME nm /\
  lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
  max_live_eom Ct = SOME eom ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s) Ct vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ptr_stage_paired_bridge_upto) >>
  strip_tac >>
  `C.ctx_entry = Ct.ctx_entry` by fs[ctx_pass_stage_def] >>
  `vs.vs_vars = FEMPTY` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `!ht at. ptr_chrono_history vs Ct ht at /\ gas_cut n vs at.po_state ==>
     (?h a done tokens registry births PT TG saved entries H calls ws.
       ptr_paired_prefix R lp positions lo vs C Ct h a ht at done tokens registry births PT TG saved entries H calls ws /\
       a.po_inst.inst_opcode <> NOP /\
       at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
     (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
       revert_forward_pair bb i j /\
       i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)` by (
    pure_rewrite_tac [GSYM AND_IMP_INTRO] >>
    match_mp_tac ptr_paired_history_coverage_upto >>
    rpt conj_tac
    >~ [`ptr_chrono_step`]
    >- (rpt strip_tac >> drule_all ptr_paired_universal_extension_upto >>
        disch_then ACCEPT_TAC) >>
    fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  irule ptr_paired_coverage_static_mem_upto >> simp[] >>
  qexistsl [`C`, `fn`, `lbl`, `lo`, `nm`, `rpolicy`] >> simp[] >>
  (reverse conj_tac >- metis_tac[]) >>
  qexistsl [`R`, `lp`, `positions`] >> simp[] >>
  rpt strip_tac >>
  `gas_cut n vs a.po_state` by metis_tac[ptr_paired_prefix_gas_cut] >>
  drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ptr_paired_current_static_bound_upto >> simp[] >>
  disch_then (qspecl_then [`rpolicy`, `n`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> simp[]
QED

Theorem concretize_stage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom ==>
  mem_inv (static_mem_ok eom) C' vs
Proof
  rpt gen_tac >> strip_tac >>
  `?nm fn lbl. C.ctx_entry = SOME nm /\
    lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl` by
    metis_tac[mem_inv_raw_reachable] >>
  `ptr_discipline_upto lo (SUC (LENGTH vs.vs_gas_readings)) C vs` by
    metis_tac[ptr_discipline_upto_whole] >>
  `mem_inv (\ctx fn inst s. gas_cut (SUC (LENGTH vs.vs_gas_readings)) vs s ==>
      static_mem_ok eom ctx fn inst s) C' vs` suffices_by simp[SF ETA_ss] >>
  drule_all concretize_stage_static_mem_ptr_upto >> disch_then ACCEPT_TAC
QED

Theorem concretize_stage_static_mem_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_ptr_safe_upto D lo n C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  C.ctx_entry = SOME nm /\
  lookup_function nm C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl /\
  max_live_eom Ct = SOME eom ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s) Ct vs
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
   ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\
   ptr_discipline_upto lo n C vs` by fs[o1_ptr_safe_upto_def] >>
  drule_all concretize_stage_static_mem_ptr_upto >> disch_then ACCEPT_TAC
QED
