(*
 * ConcretizeMemLoc's stage contract, row 3's taint containment with
 * DALLOCA: the output's taint at call requests and halts stays within
 * the dead bytes, as the input's does.
 *
 * TOP-LEVEL:
 *   concretize_stage_taint_within
 *)
Theory concretizeStageTaint
Ancestors
  concretizeStageStatic
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrUniversalExtension concretizePtrCoverageStaticMem
  concretizePtrFrameRetpcShape
  concretizePtrDallocaNoEom concretizePtrDallocaPairedObservation
  concretizePtrChronologicalHistory lowerDloadRevertSuffix
  lowerDloadPtrRawReachable frameAllocationOwnership
  venomExecSemantics venomState contextCodegenRel unitTransformDefs
  concretizeAllocationFree ptrStaticDiscipline pointerConfinedDefs
  pointerConfinedProps pointerClosure lowerDloadPtrClosure passSharedDefs
  passSharedProps passTransform venomInst list pred_set

(* Coverage and both consumers retain one choice of the stage bridge. *)
Theorem concretize_stage_taint_within:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) ==>
  taint_within D C' vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?names. callee_first names C.ctx_functions`
    (qx_choose_then `names` assume_tac) >>
  Cases_on `max_live_eom C'`
  >- (irule ptr_dalloca_no_eom_taint_within >> metis_tac[]) >>
  rename1 `max_live_eom C' = SOME eom` >>
  `(ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp)` by simp[] >>
  drule ptr_stage_paired_bridge >>
  disch_then (qspecl_then [`vs`,`lo`,`eom`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `C.ctx_entry = C'.ctx_entry` by fs[ctx_pass_stage_def] >>
  `vs.vs_vars = FEMPTY` by fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `!ht at. ptr_chrono_history vs C' ht at ==>
    (?h a done tokens registry births PT TG saved entries H calls ws.
      ptr_paired_prefix R lp positions lo vs C C'
        h a ht at done tokens registry births PT TG saved entries H calls ws /\
      EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done /\
      a.po_inst.inst_opcode <> NOP /\
      at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
    (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
      revert_forward_pair bb i j /\ i < at.po_state.vs_inst_idx /\
      at.po_state.vs_inst_idx <= j)` by
    (rpt gen_tac >> disch_tac >> irule ptr_paired_history_coverage_safe >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         drule_all ptr_paired_universal_extension >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  rewrite_tac[taint_within_def] >> conj_tac
  >- (map_every qx_gen_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`fuel`,`post`] >>
      strip_tac >>
      `MEM fn C'.ctx_functions` by
        (drule frame_reachable_functions_member >> simp[]) >>
      `ALL_DISTINCT (fn_labels fn)` by
        (qpat_assum `EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions`
           (mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
      drule ptr_reachable_has_chrono_history >>
      disch_then (qx_choose_then `ht` assume_tac) >>
      qpat_assum `!ht at. ptr_chrono_history _ _ _ _ ==> _`
        (drule_then strip_assume_tac)
      >- (mp_tac (Q.INST [`at` |-> `ptr_observe stk PG G tn fn inst s`]
            ptr_dalloca_paired_observation_taint) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then (mp_tac o CONJUNCT1) >>
          disch_then (qspecl_then [`fuel`,`post`] mp_tac) >>
          simp[NoAsms, ptr_observe_def] >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC) >>
      fs[ptr_observe_def] >>
      drule_all active_inst_block_lookup >> strip_tac >> gvs[] >>
      mp_tac (Q.INST [`ctx` |-> `C'`, `t` |-> `post`] ld_revert_pair_suffix_step) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp[next_inst_def] >> strip_tac >> fs[]) >>
  map_every qx_gen_tac [`th`,`tt`,`Rt`] >> rewrite_tac[final_taint_def] >>
  disch_then (qx_choose_then `stk` (qx_choose_then `PG` (qx_choose_then `G`
    (qx_choose_then `tn` (qx_choose_then `fn` (qx_choose_then `inst`
      (qx_choose_then `s` (qx_choose_then `fuel` strip_assume_tac)))))))) >>
  qpat_x_assum `tt = step_taint inst s th tn` SUBST_ALL_TAC >>
  qpat_x_assum `Rt = ret_taint tn inst s` SUBST_ALL_TAC >>
  `MEM fn C'.ctx_functions` by
    (drule frame_reachable_functions_member >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    (qpat_assum `EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  drule ptr_reachable_has_chrono_history >>
  disch_then (qx_choose_then `ht` assume_tac) >>
  qpat_assum `!ht at. ptr_chrono_history _ _ _ _ ==> _`
    (drule_then strip_assume_tac)
  >- (mp_tac (Q.INST [`at` |-> `ptr_observe stk PG G tn fn inst s`]
        ptr_dalloca_paired_observation_taint) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (mp_tac o CONJUNCT2) >>
      disch_then (qspecl_then [`fuel`,`th`] mp_tac) >>
      simp[NoAsms, ptr_observe_def] >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  fs[ptr_observe_def] >>
  drule_all active_inst_block_lookup >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [`ctx` |-> `C'`, `t` |-> `th`] ld_revert_pair_suffix_step) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED
