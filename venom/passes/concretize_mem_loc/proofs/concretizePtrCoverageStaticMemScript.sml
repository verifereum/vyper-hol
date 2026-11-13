(*
 * Static memory bound of every target observation, from full paired-prefix
 * coverage of the target's chronological histories.
 *)
Theory concretizePtrCoverageStaticMem
Ancestors
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrStorageReadProducer unitMemInv o1PassLift
  concretizePtrCoverageStaticMemReachability concretizePtrCurrentObservation
  o1PassContract concretizePtrPairedFields concretizePtrChronologicalHistory list pair
  pointerConfinedDefs memLocDefs passSharedDefs venomState pred_set finite_map
  contextCodegenRel concretizePtrOperationalOpcodes stepWriteFootprintBase
  venomExecProofs venomWf venomExecSemantics venomInst codegenRel lowerDloadDefs
  ptrDisciplineEmptyTaint ptrDiscipline ctxLookupAgree
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrOwnershipErasure concretizePtrOpaqueRetpc
  concretizePtrSharedFields concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrObservationInterface concretizePtrParamSupport concretizeStepStructure
  concretizeMemLocDefs unitShapeDefs unitLabelMapIdentity frameRawEndpoints
  frameHistoryInstructions ctxLookupAgreeHelpers venomInstProofs1

(* ===== Target fmp facts in a revert-forwarding window ===== *)

(* A block entry stops at the end of the PHI prefix, which lies at or
   before the RETURNDATACOPY that opens a revert-forwarding pair. *)
Theorem enters_block_before_revert_window:
  enters_block fn s s1 /\ ALL_DISTINCT (fn_labels fn) /\
  lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j ==>
  s1.vs_inst_idx <= i
Proof
  strip_tac >> drule frameHistoryInstructionsTheory.enters_block_entry_index >>
  disch_then (qx_choose_then `eb` strip_assume_tac) >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME eb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
  `eb = bb` by gvs[] >> gvs[] >>
  spose_not_then assume_tac >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by
    (irule venomExecProofsTheory.phi_prefix_length_el_phi >> decide_tac) >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def, get_instruction_def] >> rpt strip_tac >> gvs[]
QED

(* Every suspended frame of a chronological observation waits at an
   active INVOKE. *)
Theorem ptr_chrono_history_suspended_invokes:
  !vs0 ctx h a. ptr_chrono_history vs0 ctx h a ==>
    EVERY (\f. active_inst f.cf_fn f.cf_inst f.cf_state /\
               f.cf_inst.inst_opcode = INVOKE) a.po_stack
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> simp[ptr_observe_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> strip_tac >> gvs[ptr_observe_def]
QED

(* A chronological step that lands strictly inside a revert-forwarding
   window is an ordinary step over the RETURNDATACOPY or one of the
   ASSIGNs after it, so it keeps both free-memory-pointer fields. *)
Theorem ptr_chrono_step_window_fmp:
  ptr_chrono_step ctx a b /\
  EVERY (\f. active_inst f.cf_fn f.cf_inst f.cf_state /\
             f.cf_inst.inst_opcode = INVOKE) a.po_stack /\
  ALL_DISTINCT (fn_labels b.po_fn) /\
  lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < b.po_state.vs_inst_idx /\ b.po_state.vs_inst_idx <= j ==>
  b.po_state.vs_fmp = a.po_state.vs_fmp /\
  b.po_state.vs_initial_fmp = a.po_state.vs_initial_fmp
Proof
  simp[Once ptr_chrono_step_cases] >> strip_tac >> gvs[ptr_observe_def]
  >- (`step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
      `s'.vs_current_bb = s.vs_current_bb` by
        (drule_all venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]) >>
      qpat_x_assum `active_inst fn inst s` mp_tac >>
      simp[active_inst_def] >> disch_then (qx_choose_then `bb0` strip_assume_tac) >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb0` by
        (irule venomExecProofsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
      `bb0 = bb` by gvs[] >>
      `get_instruction bb s.vs_inst_idx = SOME inst` by gvs[get_instruction_def] >>
      `inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = ASSIGN` by
        (qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
         simp[revert_forward_pair_def] >> strip_tac >>
         Cases_on `s.vs_inst_idx = i` >- gvs[] >>
         disj2_tac >> first_x_assum irule >> qexists `s.vs_inst_idx` >> simp[]) >>
      `s'.vs_fmp = s.vs_fmp` by
        (irule venomInstProofs1Theory.step_inst_base_preserves_fmp_ordinary >>
         qexists `inst` >> fs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
      metis_tac[ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp])
  >- (drule_all enters_block_before_revert_window >> strip_tac >>
      `F` suffices_by rewrite_tac[] >> decide_tac)
  >- (drule_all enters_block_before_revert_window >> strip_tac >>
      `F` suffices_by rewrite_tac[] >> decide_tac) >>
  `s'.vs_current_bb = f.cf_state.vs_current_bb` by
    (`s'.vs_current_bb =
        (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)).vs_current_bb` by
       (qpat_x_assum `bind_outputs _ _ _ = SOME _` mp_tac >>
        qspec_then `\s. s.vs_current_bb` mp_tac
          venomInstProofs1Theory.bind_outputs_preserves >>
        simp[update_var_def] >> metis_tac[]) >>
     Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  qpat_x_assum `active_inst f.cf_fn f.cf_inst f.cf_state` mp_tac >>
  simp[active_inst_def] >> disch_then (qx_choose_then `bb0` strip_assume_tac) >>
  `lookup_block f.cf_state.vs_current_bb f.cf_fn.fn_blocks = SOME bb0` by
    (irule venomExecProofsTheory.MEM_lookup_block >> fs[fn_labels_def]) >>
  `bb0 = bb` by gvs[] >>
  `get_instruction bb f.cf_state.vs_inst_idx = SOME f.cf_inst` by
    gvs[get_instruction_def] >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def] >> strip_tac >>
  Cases_on `f.cf_state.vs_inst_idx = i` >- gvs[] >>
  first_x_assum (qspecl_then [`f.cf_state.vs_inst_idx`, `f.cf_inst`] mp_tac) >>
  simp[]
QED

(* Under the coverage hypothesis, every target observation has
   initial_fmp <= fmp: outside a revert-forwarding window the paired
   source supplies it, inside one the step into the window keeps it. *)
Theorem ptr_coverage_history_fmp[local]:
  !vs0 ctx h a. ptr_chrono_history vs0 ctx h a ==>
    EVERY (\g. ALL_DISTINCT (fn_labels g)) ctx.ctx_functions /\
    (!ht at. ptr_chrono_history vs0 ctx ht at ==>
       w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp \/
       ?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
         revert_forward_pair bb i j /\
         i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j) ==>
    w2n a.po_state.vs_initial_fmp <= w2n a.po_state.vs_fmp
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      `ptr_chrono_history vs0 ctx [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
         (ptr_observe [] [] FEMPTY entry_taint fn inst s1)` by
        metis_tac[ptr_chrono_history_rules] >>
      qpat_x_assum `!ht at. _` (drule_then
        (DISJ_CASES_THEN2 ACCEPT_TAC strip_assume_tac)) >>
      gvs[ptr_observe_def] >>
      `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
      `ALL_DISTINCT (fn_labels fn)` by fs[EVERY_MEM] >>
      drule_all enters_block_before_revert_window >> decide_tac) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `ptr_chrono_step ctx a b` >>
  rename1 `ptr_chrono_history vs0 ctx h a` >>
  `w2n a.po_state.vs_initial_fmp <= w2n a.po_state.vs_fmp` by
    (first_x_assum irule >> metis_tac[]) >>
  `ptr_chrono_history vs0 ctx (h ++ [b]) b` by
    metis_tac[ptr_chrono_history_rules] >>
  qpat_x_assum `!ht at. _` (drule_then
    (DISJ_CASES_THEN2 ACCEPT_TAC strip_assume_tac)) >>
  `ALL_DISTINCT (fn_labels b.po_fn)` by
    (drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> fs[EVERY_MEM]) >>
  qpat_assum `ptr_chrono_history vs0 ctx h a`
    (assume_tac o MATCH_MP ptr_chrono_history_suspended_invokes) >>
  drule_all ptr_chrono_step_window_fmp >> strip_tac >> simp[]
QED

(* The paired source state gives the target's free-memory-pointer fields
   and DALLOCA's no-wrap bound. *)
Theorem ptr_paired_target_static_fields[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ mem_inv raw_mem_ok C vs /\ ptr_discipline lo C vs /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp /\
  dalloca_no_wrap at.po_inst at.po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    (drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `raw_mem_ok C a.po_fn a.po_inst a.po_state` by
    (drule_all (Q.INST [`M` |-> `raw_mem_ok`] frame_reachable_mem_inv) >> simp[]) >>
  `a.po_state.vs_initial_fmp = at.po_state.vs_initial_fmp /\
   a.po_state.vs_fmp = at.po_state.vs_fmp` by
    (fs[ptr_paired_sample_def] >> drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  conj_tac >- (fs[raw_mem_ok_def] >> metis_tac[]) >>
  Cases_on `a.po_inst.inst_opcode = DALLOCA`
  >- (`at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
      `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
         a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
        (fs[ptr_paired_sample_def] >>
         metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
      suspend "dalloca") >>
  `at.po_inst.inst_opcode <> DALLOCA` by
    (rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
     gvs[mk_assign_inst_def, mk_nop_inst_def]) >>
  simp[dalloca_no_wrap_def]
QED

Resume ptr_paired_target_static_fields[dalloca]:
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `MEM a.po_fn C.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by fs[fn_shape_ok_def] >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  qpat_assum `ptr_discipline _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  simp[dalloca_no_wrap_def] >> rpt strip_tac >>
  `MEM sz_op a.po_inst.inst_operands` by simp[] >>
  `op_taint a.po_taint sz_op = {}` by
    (spose_not_then assume_tac >> fs[taint_ok_def] >>
     first_x_assum drule >> simp[]) >>
  `op_prov a.po_prov sz_op = NONE` by
    (Cases_on `sz_op` >> simp[op_prov_def] >>
     spose_not_then assume_tac >>
     `s IN fn_pv P a.po_fn` by
       (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def] >>
     simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `eval_operand sz_op a.po_state = SOME sz` by
    (drule ptr_mixed_scalar_eval >> disch_then drule >>
     disch_then (qspec_then `sz_op` mp_tac) >> fs[EVERY_MEM]) >>
  fs[raw_mem_ok_def, dalloca_no_wrap_def]
QED

Finalise ptr_paired_target_static_fields

Theorem ptr_paired_coverage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ mem_inv dload_headroom_ok C vs /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ unitShapeDefs$retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
    !ht at. ptr_chrono_history vs C' ht at ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)) ==>
  mem_inv (static_mem_ok eom) C' vs
Proof
  strip_tac >>
  `C'.ctx_entry = C.ctx_entry` by fs[ctx_pass_stage_def] >>
  `?name fn lbl. C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\ fn_entry_label fn = SOME lbl` by
    metis_tac[mem_inv_raw_reachable] >>
  rewrite_tac[mem_inv_raw_reachable] >> conj_tac
  >- (drule_all list_rel_lookup_function >>
      disch_then (qspec_then `name` mp_tac) >> simp[] >>
      Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
      strip_tac >> fs[ptr_paired_code_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  `w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (drule ptr_coverage_history_fmp >> impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         rpt strip_tac >> qpat_x_assum `!ht at. _` drule >> strip_tac
         >- (disj1_tac >>
             drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
               ptr_paired_target_static_fields >> simp[]) >>
         disj2_tac >> metis_tac[]) >>
     simp[ptr_observe_def]) >>
  qpat_x_assum `!ht at. _` drule >> strip_tac
  >- (`dalloca_no_wrap inst s` by
        (fs[ptr_observe_def] >> drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
           ptr_paired_target_static_fields >> simp[]) >>
      drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
        ptr_paired_current_static_bound >>
      simp[] >>
      disch_then (qspec_then `rpolicy` mp_tac) >>
      (impl_tac >- metis_tac[]) >>
      gvs[static_mem_ok_def, inst_mem_ranges_def, EVERY_MEM, FORALL_PROD,
          ptr_observe_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[ptr_observe_def] >>
  `dalloca_no_wrap inst s` by
    (simp[dalloca_no_wrap_def] >> strip_tac >>
     `MEM fn' C'.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
     `ALL_DISTINCT (fn_labels fn')` by gvs[EVERY_MEM] >>
     drule raw_reachable_active >> rewrite_tac[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> fs[fn_labels_def]) >>
     `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
     `get_instruction bb s.vs_inst_idx = SOME inst` by fs[get_instruction_def] >>
     qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     simp[revert_forward_pair_def] >> strip_tac >>
     Cases_on `s.vs_inst_idx = j` >- gvs[] >>
     first_x_assum (qspecl_then [`s.vs_inst_idx`, `inst`] mp_tac) >> simp[]) >>
  Cases_on `s.vs_inst_idx = j`
  >- (simp[static_mem_ok_def, in_revert_forward_def, revert_forward_at_def] >>
      metis_tac[]) >>
  `MEM fn' C'.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `ALL_DISTINCT (fn_labels fn')` by gvs[EVERY_MEM] >>
  drule raw_reachable_active >>
  rewrite_tac[active_inst_def] >> strip_tac >>
  `lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by fs[get_instruction_def] >>
  `inst.inst_opcode = ASSIGN` by
    (qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     simp[revert_forward_pair_def] >> strip_tac >>
     first_x_assum irule >> qexists `s.vs_inst_idx` >> simp[]) >>
  simp[static_mem_ok_def, inst_mem_ranges_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

