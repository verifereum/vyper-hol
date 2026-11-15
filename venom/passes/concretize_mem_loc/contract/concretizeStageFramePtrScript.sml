(*
 * ConcretizeMemLoc's stage contract, row 3's run-time pointer conjunct
 * with DALLOCA: every reachable access of the output is in a site of its
 * provenance, or below the layout end, and its taint use is allowed.
 *
 * TOP-LEVEL:
 *   concretize_stage_frame_ptr_ok
 *)
Theory concretizeStageFramePtr
Ancestors
  concretizePtrForwardingTaintHistory
  concretizePtrDallocaFrameEndpoint concretizePtrChronologicalHistory
  concretizePtrStructuralTrace concretizePtrHistoryObservation
  concretizePtrOwnerPath
  concretizePtrDallocaRuntimeHistory concretizePtrDallocaGhostHistory
  concretizeStageStatic concretizePtrDallocaHistoricalPersistent
  concretizePtrDallocaHistoricalMemory concretizePtrDallocaHistoricalRead
  concretizePtrDallocaMemorySteps concretizePtrDallocaStageCoverage
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrUniversalExtension concretizePtrCoverageStaticMem
  concretizePtrFrameRetpcShape
  concretizeAllocationFree ptrStaticDiscipline pointerConfinedDefs
  pointerConfinedProps pointerClosure lowerDloadPtrClosure passSharedDefs
  concretizeStepContract concretizeStepShape concretizePtrPairedFields
  lowerDloadPtrForward memSafeRun venomWf venomExecProofs
  frameAllocationOwnership contextCodegenRel codegenRel
  passSharedProps passTransform venomInst list pred_set arithmetic words

(* Safe coverage supplies paired endpoints; the exceptional forwarding
   interval uses the actual opener and ASSIGN chronology. *)
Theorem concretize_stage_frame_ptr_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) /\
  max_live_eom C' = SOME eom ==>
  !stk PG G tn fn inst s.
    frame_reachable vs C' stk PG G tn fn inst s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eom <= w2n vs.vs_initial_fmp` by metis_tac[] >>
  `EVERY wf_function C'.ctx_functions /\
   EVERY (\fn. EVERY inst_wf (fn_insts fn)) C'.ctx_functions` by
    (mp_tac ptr_stage_paired_bridge >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `shape_R`
       (qx_choose_then `shape_lp`
         (qx_choose_then `shape_positions` strip_assume_tac))) >>
     `!k. k < LENGTH C'.ctx_functions ==>
       o1_fn_shape C (EL k C'.ctx_functions)` by
       (qx_gen_tac `k` >> disch_tac >>
        `k < LENGTH C.ctx_functions` by fs[LIST_REL_EL_EQN] >>
        `ptr_paired_code shape_R shape_lp shape_positions
          (EL k C.ctx_functions) (EL k C'.ctx_functions)` by
          fs[LIST_REL_EL_EQN] >>
        `o1_fn_shape C (EL k C.ctx_functions)` by
          fs[o1_ctx_shape_def, EVERY_EL] >>
        `o1_fn_shape C (concretize_function_with_positions
           (shape_lp (EL k C.ctx_functions)) (EL k C.ctx_functions))` by
          simp[concretize_positions_o1_fn_shape] >>
        `o1_fn_shape C (EL k C'.ctx_functions) =
          o1_fn_shape C (concretize_function_with_positions
            (shape_lp (EL k C.ctx_functions)) (EL k C.ctx_functions))` by
          (irule concretize_blocks_o1_shape >>
           fs[ptr_paired_code_def, concretize_function_with_positions_def] >>
           metis_tac[]) >> simp[]) >>
     fs[EVERY_EL, o1_fn_shape_def, fn_inst_wf_def, fn_insts_def,
        fn_insts_blocks_MEM, EVERY_MEM] >>
     metis_tac[MEM_EL, fn_insts_blocks_MEM]) >>
  mp_tac ptr_dalloca_stage_frame_coverage_safe >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `?names. callee_first names C.ctx_functions` strip_assume_tac >>
  `!stk PG G tn fn inst s.
    frame_reachable vs C' stk PG G tn fn inst s /\
    inst.inst_opcode = RETURNDATACOPY ==>
    !op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ ==> _`
       (qspecl_then [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
     >- (`access_ok eom G fn inst s /\ taint_ok fn tn inst s` by
           (mp_tac (Q.INST [`at` |-> `ptr_observe stk PG G tn fn inst s`]
             ptr_dalloca_paired_frame_ptr) >>
            (impl_tac >- (simp[ptr_observe_def] >>
              rpt conj_tac >> first_assum ACCEPT_TAC)) >>
            simp[ptr_observe_def]) >>
         qpat_assum `taint_ok fn tn inst s`
           (mp_tac o CONJUNCT1 o REWRITE_RULE[taint_ok_def]) >>
         qpat_assum `inst.inst_opcode = RETURNDATACOPY` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         qpat_x_assum `!operand. _` (qspec_then `op` mp_tac) >>
         qpat_x_assum `inst.inst_opcode = RETURNDATACOPY` SUBST1_TAC >> simp[]) >>
     `active_inst fn inst s` by
       (drule ptr_owner_frame_active >> simp[]) >>
     `ALL_DISTINCT (fn_labels fn)` by
       (drule frame_reachable_functions_member >>
        fs[EVERY_MEM, wf_function_def]) >>
     `get_instruction bb s.vs_inst_idx = SOME inst` by
       (qpat_assum `active_inst fn inst s`
          (qx_choose_then `active_bb` strip_assume_tac o
            REWRITE_RULE[active_inst_def]) >>
        `lookup_block s.vs_current_bb fn.fn_blocks = SOME active_bb` by
          (irule MEM_lookup_block >> fs[fn_labels_def]) >>
        gvs[get_instruction_def]) >>
     `i <= s.vs_inst_idx` by decide_tac >>
     drule_all revert_forward_pair_interval_opcode >> strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ ==> _`
    (qspecl_then [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
  >- (mp_tac (Q.INST [`at` |-> `ptr_observe stk PG G tn fn inst s`]
        ptr_dalloca_paired_frame_ptr) >>
      (impl_tac >- (simp[ptr_observe_def] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp[ptr_observe_def]) >>
  `active_inst fn inst s` by
    (drule ptr_owner_frame_active >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    (drule frame_reachable_functions_member >>
     fs[EVERY_MEM, wf_function_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_assum `active_inst fn inst s`
       (qx_choose_then `active_bb` strip_assume_tac o
         REWRITE_RULE[active_inst_def]) >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME active_bb` by
       (irule MEM_lookup_block >> fs[fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  `i <= s.vs_inst_idx` by decide_tac >>
  drule_all revert_forward_pair_interval_opcode >> strip_tac >> gvs[]
  >- simp[access_ok_def, taint_ok_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def] >>
  `in_revert_forward fn s` by
    (simp[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  suspend "closing_revert"
QED

Resume concretize_stage_frame_ptr_ok[closing_revert]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `!b op. MEM b h /\ b.po_inst.inst_opcode = RETURNDATACOPY /\
    MEM op b.po_inst.inst_operands ==> op_taint b.po_taint op = {}` by
    (rpt gen_tac >> strip_tac >>
     `frame_reachable vs C' b.po_stack b.po_params b.po_prov b.po_taint
       b.po_fn b.po_inst b.po_state` by
       (drule ptr_chrono_history_reachable >>
        fs[EVERY_MEM, ptr_observation_reachable_def]) >>
     qpat_assum `!stk PG G tn fn inst s.
       frame_reachable vs C' stk PG G tn fn inst s /\
       inst.inst_opcode = RETURNDATACOPY ==> _`
       (qspecl_then [`b.po_stack`,`b.po_params`,`b.po_prov`,`b.po_taint`,
         `b.po_fn`,`b.po_inst`,`b.po_state`] mp_tac) >>
     simp[]) >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (mp_tac (Q.INST [`C` |-> `C'`, `j` |-> `s.vs_inst_idx`,
      `a` |-> `ptr_observe stk PG G tn fn inst s`]
      concretizePtrForwardingTaintHistoryTheory.ptr_chrono_forward_revert_operands_clean) >>
     (impl_tac >- (simp[ptr_observe_def] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[ptr_observe_def]) >>
  simp[access_ok_def, taint_ok_def, about_to_revert_def] >> metis_tac[]
QED

Finalise concretize_stage_frame_ptr_ok
