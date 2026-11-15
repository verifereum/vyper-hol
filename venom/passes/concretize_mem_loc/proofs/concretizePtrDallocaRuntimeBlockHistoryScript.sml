Theory concretizePtrDallocaRuntimeBlockHistory
Ancestors
  concretizePtrDallocaRuntimeBlock concretizePtrDallocaGhostInterface
  concretizePtrMixedPhi
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrHistoricalWriteExclusion
  concretizePtrLifetime frameAllocationOwnership o1PassContract venomWf
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  o1FrameLockstep venomExecProofs venomExecSemantics opcodeClass
  ptrDiscipline venomState venomInst finite_map list rich_list arithmetic pred_set

Theorem ptr_dalloca_runtime_chrono_block:
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' /\
  ptr_chrono_step Ct at bt /\ at.po_inst = a.po_inst /\
  (a.po_inst.inst_opcode = JMP \/ a.po_inst.inst_opcode = JNZ \/
   a.po_inst.inst_opcode = DJMP) /\
  ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var a.po_state
    at.po_prov at.po_taint.t_var at.po_state /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
    FLOOKUP at.po_prov v = SOME site) /\
  at.po_fn.fn_blocks =
    (concretize_function_with_positions p a.po_fn).fn_blocks /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  b.po_state.vs_current_bb = bt.po_state.vs_current_bb /\
  b.po_state.vs_prev_bb = bt.po_state.vs_prev_bb ==>
  (ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
   (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TG' v = NONE) /\
   (!v site. FLOOKUP TG' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
     FLOOKUP bt.po_prov v = SOME site)) /\
  PT' = PT /\ saved' = saved /\
  b.po_params = a.po_params /\ bt.po_params = at.po_params /\
  b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack /\
  b.po_state.vs_params = a.po_state.vs_params /\
  bt.po_state.vs_params = at.po_state.vs_params
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    (fs[is_terminator_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `!fuel ctx s s'. step_inst fuel ctx a.po_inst s = OK s' ==>
    s'.vs_params = s.vs_params` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `a.po_inst.inst_opcode = JMP \/ _` strip_assume_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def] >>
     simp[AllCaseEqs(), jump_to_def] >> rpt strip_tac >> gvs[]) >>
  `!fuel sr fuelt tr s1 t1.
    step_inst fuel C a.po_inst a.po_state = OK sr /\
    step_inst fuelt Ct at.po_inst at.po_state = OK tr /\
    enters_block a.po_fn sr s1 /\ enters_block at.po_fn tr t1 /\
    (!v. phi_eff sr.vs_prev_bb v (block_insts a.po_fn sr.vs_current_bb) =
      phi_eff tr.vs_prev_bb v (block_insts at.po_fn tr.vs_current_bb)) ==>
    ptr_dalloca_ghost_vars
      (entry_prov a.po_fn sr a.po_prov)
      (entry_taint_vars a.po_fn sr a.po_taint).t_var s1
      (entry_prov at.po_fn tr at.po_prov)
      (entry_taint_vars at.po_fn tr at.po_taint).t_var t1 /\
    (!v site. FLOOKUP (entry_prov at.po_fn tr at.po_prov) v = SOME site ==>
      FLOOKUP (entry_prov a.po_fn sr TG) v = NONE) /\
    (!v site. FLOOKUP (entry_prov a.po_fn sr TG) v = NONE /\
      FLOOKUP (entry_prov a.po_fn sr a.po_prov) v = SOME site ==>
      FLOOKUP (entry_prov at.po_fn tr at.po_prov) v = SOME site)` by
    (map_every qx_gen_tac [`fuel`,`sr`,`fuelt`,`tr`,`s1`,`t1`] >> strip_tac >>
     `ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var sr
       at.po_prov at.po_taint.t_var tr` by
       (imp_res_tac step_terminator_preserves_vars >>
        fs[ptr_dalloca_ghost_vars_def] >> metis_tac[]) >>
     irule ptr_dalloca_runtime_block >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def] >> strip_tac >>
  gvs[ptr_observation_component_equality]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >>
    disch_then (mp_tac o MATCH_MP step_inst_base_intret_opcodes) >>
    strip_tac >> gvs[]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def] >> strip_tac >>
  gvs[ptr_observation_component_equality]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >>
    disch_then (mp_tac o MATCH_MP step_inst_base_intret_opcodes) >>
    strip_tac >> gvs[]) >>
  rename1 `enters_block a.po_fn source_raw b.po_state` >>
  rename1 `enters_block at.po_fn target_raw bt.po_state` >>
  `!v. phi_eff source_raw.vs_prev_bb v
      (block_insts a.po_fn source_raw.vs_current_bb) =
    phi_eff target_raw.vs_prev_bb v
      (block_insts at.po_fn target_raw.vs_current_bb)` by
    (irule ptr_positions_enters_phi_eff >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!fuel sr fuelt tr s1 t1. _` (drule_all_then mp_tac) >>
  imp_res_tac ptr_dalloca_runtime_block_params >>
  qpat_x_assum `!fuel ctx s s'. _` imp_res_tac >>
  simp[]
QED

Theorem ptr_dalloca_historical_runtime_block:
  ptr_paired_prefix R lp positions lo vs C Ct
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\ n0 = EL q done /\
  EL n0 H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ptr_tagged_chrono_step C (HD ts0) (EL n0 h) (EL (SUC n0) h)
    PT0 TG0 sv0 PT' TG' saved' /\
  ((EL n0 h).po_inst.inst_opcode = JMP \/
   (EL n0 h).po_inst.inst_opcode = JNZ \/
   (EL n0 h).po_inst.inst_opcode = DJMP) /\
  ptr_dalloca_ghost_vars (EL n0 h).po_prov (EL n0 h).po_taint.t_var
    (EL n0 h).po_state (EL q ht).po_prov (EL q ht).po_taint.t_var
    (EL q ht).po_state /\
  (!v site. FLOOKUP (EL q ht).po_prov v = SOME site ==> FLOOKUP TG0 v = NONE) /\
  (!v site. FLOOKUP TG0 v = NONE /\ FLOOKUP (EL n0 h).po_prov v = SOME site ==>
    FLOOKUP (EL q ht).po_prov v = SOME site) ==>
  (ptr_dalloca_ghost_vars (EL (SUC n0) h).po_prov
    (EL (SUC n0) h).po_taint.t_var (EL (SUC n0) h).po_state
    (EL (SUC q) ht).po_prov (EL (SUC q) ht).po_taint.t_var
    (EL (SUC q) ht).po_state /\
   (!v site. FLOOKUP (EL (SUC q) ht).po_prov v = SOME site ==>
     FLOOKUP TG' v = NONE) /\
   (!v site. FLOOKUP TG' v = NONE /\
     FLOOKUP (EL (SUC n0) h).po_prov v = SOME site ==>
     FLOOKUP (EL (SUC q) ht).po_prov v = SOME site)) /\
  PT' = PT0 /\ saved' = sv0 /\
  (EL (SUC n0) h).po_params = (EL n0 h).po_params /\
  (EL (SUC q) ht).po_params = (EL q ht).po_params /\
  (EL (SUC n0) h).po_stack = (EL n0 h).po_stack /\
  (EL (SUC q) ht).po_stack = (EL q ht).po_stack /\
  (EL (SUC n0) h).po_state.vs_params = (EL n0 h).po_state.vs_params /\
  (EL (SUC q) ht).po_state.vs_params = (EL q ht).po_state.vs_params
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `n0 < LENGTH h /\ q < LENGTH ht /\ SUC q < LENGTH ht` by
    (fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >> metis_tac[]) >>
  `ptr_chrono_history vs C h endpoint` by metis_tac[ptr_structural_trace_source] >>
  `ptr_observation_reachable vs C (EL n0 h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> metis_tac[]) >>
  `MEM (EL n0 h).po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >> metis_tac[frame_reachable_functions_member]) >>
  `wf_function (EL n0 h).po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_paired_alignment R lp positions h ht done H` by fs[ptr_paired_prefix_def] >>
  qpat_assum `ptr_paired_alignment _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[ptr_paired_alignment_def]) >>
  disch_then (qspec_then `q` mp_tac) >> simp[EL_APPEND_EQN] >> strip_tac >>
  `(EL q ht).po_inst = (EL n0 h).po_inst` by
    (`(EL (EL q done) h).po_inst.inst_id = (EL q ht).po_inst.inst_id` by
       metis_tac[ptr_trace_departed_inst_ids] >>
     `(EL q ht).po_inst = concretize_inst_with_positions
        (lp (EL n0 h).po_fn) (EL n0 h).po_inst` by
       (irule ptr_departed_cursor_instruction >> fs[wf_function_def]) >>
     qpat_x_assum `(EL n0 h).po_inst.inst_opcode = JMP \/ _` strip_assume_tac >>
     fs[concretizeStepStructureTheory.concretize_positions_unchanged]) >>
  `ptr_chrono_step Ct (EL q ht) (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `(EL (SUC n0) h).po_state.vs_current_bb = (EL (SUC q) ht).po_state.vs_current_bb /\
   (EL (SUC n0) h).po_state.vs_prev_bb = (EL (SUC q) ht).po_state.vs_prev_bb` by
    (qpat_assum `ptr_paired_alignment _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE[ptr_paired_alignment_def]) >>
     disch_then (qspec_then `SUC q` mp_tac) >> simp[] >> strip_tac >>
     `(EL (SUC n0) h).po_state.vs_current_bb =
        (EL (EL (SUC q) (done ++ [LENGTH h - 1])) h).po_state.vs_current_bb /\
      (EL (SUC n0) h).po_state.vs_prev_bb =
        (EL (EL (SUC q) (done ++ [LENGTH h - 1])) h).po_state.vs_prev_bb` by
       (irule ptr_structural_trace_gap_control >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     fs[ptr_paired_cursor_def] >> metis_tac[]) >>
  irule (Q.INST [`p` |-> `lp (EL n0 h).po_fn`]
    (SPEC_ALL ptr_dalloca_runtime_chrono_block)) >>
  rpt (goal_assum (drule_at Any)) >>
  fs[ptr_paired_code_def, wf_function_def, EVERY_MEM] >> metis_tac[]
QED
