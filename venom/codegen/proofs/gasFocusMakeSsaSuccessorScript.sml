Theory gasFocusMakeSsaSuccessor
Ancestors
  makeSsaCurrentEdgePrefix makeSsaCurrentSuccessorRelation
  makeSsaCurrentPrefixTransport makeSsaCurrentLockstepShape makeSsaCurrentWfSsa
  cfgNormSupplySim venomExecProofs venomExecSemantics venomWfProps
  contextCodegenRel makeSsaCurrentPrefixSuffixOwner simplifyCfgBypassRootedEntry
  list rich_list

(* A completed nonhalting block supplies a prepared successor whenever
   the source successor is actually observed. No terminating run is used. *)
Theorem current_focus_prepared_successor:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks := simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\ wf_function fn' /\ wf_ssa fn' /\ fn_inst_wf fn' /\
  lookup_block l fn.fn_blocks = SOME old /\ lookup_block l fn'.fn_blocks = SOME bb /\
  raw.vs_current_bb = l /\ enters_block fn raw post /\
  done.vs_current_bb = l /\
  strict_dom_vars_defined fn' done /\ fn_reachable fn' l /\
  done.vs_inst_idx <= LENGTH bb.bb_instructions /\
  (!j x. j < done.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\ MEM x (EL j bb.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done)) /\
  exec_block k C old post = OK t /\ exec_block k C bb done = OK t' /\
  current_cut_inv fn A renamed H events l (LENGTH old.bb_instructions) t t' /\
  ~t.vs_halted /\ enters_block fn t next ==>
  ?old_h bb_h pre_h post_h done_h.
    lookup_block t.vs_current_bb fn.fn_blocks = SOME old_h /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb_h /\
    A t.vs_current_bb = current_block_annotations old_h pre_h /\
    LENGTH bb_h.bb_instructions = LENGTH pre_h + LENGTH old_h.bb_instructions /\
    next.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions) /\
    enters_block fn' t' post_h /\
    post_h.vs_inst_idx = phi_prefix_length bb_h.bb_instructions /\
    current_prefix_steps k C
      (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
        (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) post_h done_h /\
    (!j. j < LENGTH (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
        (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions)) ==>
      (EL j (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
        (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions))).inst_opcode = ASSIGN \/
      (EL j (TAKE (LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) - phi_prefix_length bb_h.bb_instructions)
        (DROP (phi_prefix_length bb_h.bb_instructions) bb_h.bb_instructions))).inst_opcode = NOP) /\
    current_cut_inv fn A renamed H events t.vs_current_bb (LENGTH (collect_phis old_h.bb_instructions)) next done_h /\
    done_h.vs_inst_idx = LENGTH pre_h + LENGTH (collect_phis old_h.bb_instructions) /\
    done_h.vs_current_bb = t.vs_current_bb /\
    strict_dom_vars_defined fn' done_h /\ fn_reachable fn' t.vs_current_bb /\
    done_h.vs_inst_idx <= LENGTH bb_h.bb_instructions /\
    (!j x. j < done_h.vs_inst_idx /\ j < LENGTH bb_h.bb_instructions /\ MEM x (EL j bb_h.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x done_h))
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `MEM old fn.fn_blocks /\ old.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `run_block k C old raw = exec_block k C old post` by
    (irule scfg_enters_block_run_block >> qexists `fn` >> simp[]) >>
  `t.vs_prev_bb = SOME l` by
    (drule supply_run_block_entry_control >>
     disch_then (qspecl_then [`raw`, `t`, `k`, `C`, `old`] mp_tac) >>
     simp[IgnAsm `fn' = _`]) >>
  `bb_well_formed old /\ EVERY inst_wf old.bb_instructions` by
    (fs[venomWfTheory.wf_function_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `post.vs_inst_idx = LENGTH (collect_phis old.bb_instructions)` by
    (qpat_x_assum `enters_block fn raw post` mp_tac >>
     simp[enters_block_def] >> rpt strip_tac >>
     simp[current_prefix_collect_length]) >>
  `post.vs_inst_idx <= LENGTH old.bb_instructions` by
    simp[livenessTransferProofsTheory.current_collect_phis_length] >>
  `MEM t.vs_current_bb (bb_succs old)` by
    (irule exec_block_current_bb_in_succs >>
     reverse conj_tac
     >- (conj_tac
         >- (qpat_x_assum `bb_well_formed old` mp_tac >>
             simp[venomWfTheory.bb_well_formed_def]) >>
         qexistsl [`C`, `k`, `post`] >> simp[IgnAsm `fn' = _`]) >>
     qpat_x_assum `bb_well_formed old` mp_tac >>
     pure_rewrite_tac[venomWfTheory.bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH old.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH old.bb_instructions)` by metis_tac[] >> decide_tac) >>
  `fn_cfg_edge fn l t.vs_current_bb` by
    (simp[venomWfTheory.fn_cfg_edge_def] >> qexists `old` >> simp[]) >>
  `t'.vs_current_bb = t.vs_current_bb` by
    fs[makeSsaCurrentCutInvTheory.current_cut_inv_def, o1FrameLockstepTheory.state_rel_def] >>
  `t.vs_current_bb = t.vs_current_bb` by simp[] >>
  drule_all current_cut_successor_prefix_relation >> strip_tac >>
  suspend "prepare"
QED

Resume current_focus_prepared_successor[prepare]:
  `next.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions)` by
    (qpat_x_assum `enters_block fn t next` mp_tac >>
     simp[enters_block_def] >> rpt strip_tac >>
     simp[current_prefix_collect_length]) >>
  `MEM bb fn'.fn_blocks /\ MEM bb' fn'.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `EVERY inst_wf bb.bb_instructions /\ EVERY inst_wf bb'.bb_instructions` by
    (fs[venomWfTheory.fn_inst_wf_compute, EVERY_MEM] >> metis_tac[]) >>
  `?new_h. lookup_block t.vs_current_bb renamed = SOME new_h /\
    bb' = if blocks_have_leading_phi fn.fn_blocks
      then simplify_current_phi_block new_h else new_h` by
    (qpat_x_assum `lookup_block t.vs_current_bb fn'.fn_blocks = _` mp_tac >>
     qpat_assum `fn' = _` SUBST1_TAC >>
     simp[makeSsaCurrentCleanupShapeTheory.current_cleanup_if_lookup] >>
     Cases_on `lookup_block t.vs_current_bb renamed` >> simp[] >> metis_tac[]) >>
  `phi_prefix_length new_h.bb_instructions = LENGTH pre +
    LENGTH (collect_phis old_h.bb_instructions)` by
    (drule_all current_prefix_actual_endpoint >> simp[]) >>
  `bb.bb_label = done.vs_current_bb` by metis_tac[lookup_block_label] >>
  `lookup_block t'.vs_current_bb fn'.fn_blocks = SOME bb'` by metis_tac[] >>
  `~t'.vs_halted` by
    fs[makeSsaCurrentCutInvTheory.current_cut_inv_def,
       o1FrameLockstepTheory.state_rel_def, stateFrameTheory.execution_frame_def] >>
  `fn_reachable fn' t.vs_current_bb` by
    (irule fn_reachable_step >> qexists `l` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     pure_rewrite_tac[venomWfTheory.fn_cfg_edge_def] >> qexists `bb` >>
     simp[IgnAsm `fn' = _`] >>
     qpat_assum `t'.vs_current_bb = t.vs_current_bb`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule exec_block_current_bb_in_succs >>
     reverse conj_tac
     >- (conj_tac
         >- (qpat_assum `wf_function fn'` mp_tac >>
             pure_rewrite_tac[venomWfTheory.wf_function_def] >> strip_tac >>
             `bb_well_formed bb` by metis_tac[] >>
             qpat_x_assum `bb_well_formed bb` mp_tac >>
             pure_rewrite_tac[venomWfTheory.bb_well_formed_def] >> metis_tac[]) >>
         qexistsl [`C`, `k`, `done`] >> simp[IgnAsm `fn' = _`]) >>
     metis_tac[passSimulationPropsTheory.wf_non_terminator_prefix]) >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- suspend "cleaned" >>
  suspend "plain"
QED

Resume current_focus_prepared_successor[cleaned]:
  `bb' = simplify_current_phi_block new_h` by asm_rewrite_tac[] >>
  `fn' = fn with fn_blocks := simplify_current_phis_if T renamed` by asm_rewrite_tac[] >>
  `fn_reachable fn' done.vs_current_bb` by metis_tac[] >>
  qabbrev_tac `cs = TAKE
    (phi_prefix_length new_h.bb_instructions - phi_prefix_length bb'.bb_instructions)
    (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` >>
  `cs = TAKE
    (phi_prefix_length new_h.bb_instructions - phi_prefix_length bb'.bb_instructions)
    (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` by simp[Abbr `cs`] >>
  drule_all current_completed_edge_cleaned_prefix_total >> strip_tac >>
  rename1 `eval_phis t' bb'.bb_instructions = OK succ_base` >>
  rename1 `current_prefix_steps k C cs _ succ_done` >>
  `enters_block fn' t'
     (succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` by
    (pure_rewrite_tac[enters_block_def] >>
     qexistsl [`bb'`, `succ_base`] >> metis_tac[]) >>
  `cs = TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) -
     phi_prefix_length bb'.bb_instructions)
     (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` by metis_tac[] >>
  `current_prefix_steps k C
     (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) -
       phi_prefix_length bb'.bb_instructions)
       (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions))
     (succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions) succ_done` by metis_tac[] >>
  qpat_assum `!post post' done fuel C. _` (drule_all_then strip_assume_tac) >>
  suspend "cleaned_silence"
QED
Resume current_focus_prepared_successor[cleaned_silence]:
  `!j. j < LENGTH cs ==> (EL j cs).inst_opcode = ASSIGN \/
      (EL j cs).inst_opcode = NOP` by
    (rpt strip_tac >>
     `j < phi_prefix_length new_h.bb_instructions - phi_prefix_length bb'.bb_instructions /\
      j < LENGTH (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions)` by
       (qpat_x_assum `j < LENGTH cs` mp_tac >>
        simp[NoAsms, Abbr `cs`, LENGTH_TAKE_EQ, LENGTH_DROP, arithmeticTheory.MIN_DEF] >>
        rpt strip_tac >> decide_tac) >>
     `EL j cs = EL (phi_prefix_length bb'.bb_instructions + j) bb'.bb_instructions` by
       (qpat_assum `j < _ - _` mp_tac >> qpat_assum `j < LENGTH (DROP _ _)` mp_tac >>
        simp[NoAsms, Abbr `cs`, EL_TAKE, EL_DROP, arithmeticTheory.ADD_COMM]) >>
     pop_assum SUBST1_TAC >>
     `phi_prefix_length bb'.bb_instructions <= phi_prefix_length bb'.bb_instructions + j /\
      phi_prefix_length bb'.bb_instructions + j < phi_prefix_length new_h.bb_instructions` by decide_tac >>
     metis_tac[simplify_current_phi_block_layout]) >>
  qexistsl [`old_h`, `bb'`, `pre`,
    `succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions`, `succ_done`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms] >>
  qpat_x_assum `!j. j < LENGTH cs ==> _` mp_tac >>
  qpat_x_assum `cs = TAKE (_ + _ - _) _` SUBST1_TAC >> simp[]
QED
Resume current_focus_prepared_successor[plain]:
  `bb' = new_h` by metis_tac[] >>
  `fn_reachable fn' done.vs_current_bb` by metis_tac[] >>
  drule_all current_completed_edge_plain_prefix_total >> strip_tac >>
  rename1 `eval_phis t' bb'.bb_instructions = OK succ_base` >>
  `enters_block fn' t'
     (succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` by
    (pure_rewrite_tac[enters_block_def] >>
     qexistsl [`bb'`, `succ_base`] >> metis_tac[]) >>
  `TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) -
     phi_prefix_length bb'.bb_instructions)
     (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions) = []` by
    (`LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) =
      phi_prefix_length bb'.bb_instructions` by metis_tac[] >>
     pop_assum (fn th => simp[NoAsms, th])) >>
  `current_prefix_steps k C
    (TAKE (LENGTH pre + LENGTH (collect_phis old_h.bb_instructions) -
      phi_prefix_length bb'.bb_instructions)
      (DROP (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions))
    (succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
    (succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions)` by
    (qpat_assum `TAKE _ _ = []` (fn th =>
      simp[NoAsms, th, makeSsaCurrentCopyPrefixRuntimeTheory.current_prefix_steps_def])) >>
  qpat_assum `!post post' done fuel C. _` (drule_all_then strip_assume_tac) >>
  `succ_base.vs_current_bb = t.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qexistsl [`old_h`, `bb'`, `pre`,
    `succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions`,
    `succ_base with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms] >>
  TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `TAKE _ _ = []` (fn th => simp[NoAsms, th])
QED
Finalise current_focus_prepared_successor
