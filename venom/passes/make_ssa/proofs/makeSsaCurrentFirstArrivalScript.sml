Theory makeSsaCurrentFirstArrival
Ancestors makeSsaCurrentExecutionHistory makeSsaCurrentActualPath makeSsaCurrentMergeSeed makeSsaCurrentDefaultAudit
  makeSsaCurrentInsertedNonself makeSsaCurrentDominanceBridge dominatorProofs
  venomExecProps venomExecProofs venomInstProps venomExecSemantics venomWf venomInst
  o1PassLift dominatorDefs makeSsaCurrentAnalysis makeSsaCurrentReinsertionSlots
  makeSsaCurrentPathBridge makeSsaCurrentTokens makeSsaCurrentReinsertionNames
  makeSsaCurrentTraceCertificate makeSsaCurrentAllocation makeSsaCurrentRenameTrace
  makeSsaCurrentPlacementCut makeSsaCurrentCertificate list rich_list

(* A projection of actual prefixes, not another execution ledger.  LRC omits
   its final vertex, so both the route and that vertex have batch witnesses. *)
Definition current_dispatched_cut_def:
  (current_dispatched_cut fn root phases (CurrentEntry fuel) st <=>
    (st.vs_current_bb = root /\ st.vs_prev_bb = NONE) \/
    ?ls p. LRC (fn_cfg_edge fn) ls root p /\
      st.vs_prev_bb = SOME p /\ fn_cfg_edge fn p st.vs_current_bb /\
      (!l. MEM l (ls ++ [p]) ==> ?phis. MEM (CurrentBatch l phis) phases)) /\
  (current_dispatched_cut fn root phases (CurrentBody fuel bb) st <=>
    ?ls. LRC (fn_cfg_edge fn) ls root st.vs_current_bb /\
      (!l. MEM l (ls ++ [st.vs_current_bb]) ==>
        ?phis. MEM (CurrentBatch l phis) phases))
End

Theorem current_lrc_extend[local]:
  !ls a p. LRC R ls a p /\ R p q ==> LRC R (ls ++ [p]) a q
Proof
  Induct >> simp[LRC_def] >> metis_tac[]
QED

Theorem current_dispatched_cut_dispatch[local]:
  current_dispatched_cut fn root phases (CurrentEntry (SUC fuel)) before /\
  lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis before bb.bb_instructions = OK post ==>
  current_dispatched_cut fn root
    (phases ++ [CurrentBatch before.vs_current_bb
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions); CurrentControl])
    (CurrentBody fuel bb) (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >>
  `post.vs_current_bb = before.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  gvs[current_dispatched_cut_def]
  >- (qexists_tac `[]` >> simp[LRC_def] >> metis_tac[]) >>
  qexists_tac `ls ++ [p]` >> simp[] >>
  conj_tac >- metis_tac[current_lrc_extend] >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem current_dispatched_cut_mono[local]:
  current_dispatched_cut fn root phases loc st /\
  (!phase. MEM phase phases ==> MEM phase more) ==>
  current_dispatched_cut fn root more loc st
Proof
  Cases_on `loc` >> simp[current_dispatched_cut_def] >> metis_tac[]
QED

Theorem current_dispatched_cut_ordinary[local]:
  current_dispatched_cut fn root phases (CurrentBody fuel bb) before /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK post ==>
  current_dispatched_cut fn root phases (CurrentBody fuel bb)
    (post with vs_inst_idx := SUC before.vs_inst_idx)
Proof
  strip_tac >>
  `post.vs_current_bb = before.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  gvs[current_dispatched_cut_def] >> metis_tac[]
QED

Theorem current_first_arrival_term_edge[local]:
  wf_function fn /\ lookup_block before.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst before = OK post /\ ~post.vs_halted ==>
  fn_cfg_edge fn before.vs_current_bb post.vs_current_bb /\
  post.vs_prev_bb = SOME before.vs_current_bb
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = before.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `before.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL before.vs_inst_idx bb.bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `LAST bb.bb_instructions = inst` by
    (gvs[bb_well_formed_def, LAST_EL] >> metis_tac[]) >>
  `MEM post.vs_current_bb (get_successors inst)` by
    metis_tac[step_inst_base_term_succs, step_inst_non_invoke] >>
  `MEM post.vs_current_bb (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  conj_tac >- (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  metis_tac[step_inst_base_term_prev_bb, step_inst_non_invoke]
QED

Theorem current_dispatched_cut_edge[local]:
  !loc before phases next result after.
  current_execution_edge fn ctx loc before phases next result after ==>
  wf_function fn /\ current_dispatched_cut fn root prior loc before ==>
  !nextloc. next = SOME nextloc /\ result = OK after ==>
    current_dispatched_cut fn root (prior ++ phases) nextloc after
Proof
  ho_match_mp_tac current_execution_edge_ind >> rpt conj_tac >> rpt gen_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[current_dispatched_cut_dispatch])
  >- (rpt strip_tac >> gvs[] >>
      irule current_dispatched_cut_mono >>
      qexists_tac `prior` >> simp[] >>
      metis_tac[current_dispatched_cut_ordinary])
  >- (rpt strip_tac >> gvs[AllCaseEqs()] >>
      drule_all current_first_arrival_term_edge >> strip_tac >>
      gvs[current_dispatched_cut_def] >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem current_dispatched_cut_prefix[local]:
  !loc before phases next result after.
  current_actual_prefix fn ctx loc before phases next result after ==>
  !prior. wf_function fn /\ current_dispatched_cut fn root prior loc before ==>
  !nextloc. next = SOME nextloc /\ result = OK after ==>
    current_dispatched_cut fn root (prior ++ phases) nextloc after
Proof
  ho_match_mp_tac current_actual_prefix_ind >> rpt conj_tac >> rpt gen_tac
  >- simp[]
  >- metis_tac[current_dispatched_cut_edge]
  >- (rpt strip_tac >>
      drule current_dispatched_cut_edge >> simp[] >>
      disch_then (qspec_then `loc'` mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspec_then `prior ++ phases` mp_tac) >>
      simp[APPEND_ASSOC]) >>
  simp[]
QED

Theorem current_actual_dispatched_route:
  wf_function fn /\ entry_block fn = SOME eb /\ fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
    (SOME (CurrentEntry remaining)) (OK before) before /\ before.vs_prev_bb = SOME p ==>
  ?ls. LRC (fn_cfg_edge fn) ls eb.bb_label p /\
    (!l. MEM l (ls ++ [p]) ==> ?phis. MEM (CurrentBatch l phis) phases)
Proof
  strip_tac >>
  `current_dispatched_cut fn eb.bb_label [] (CurrentEntry fuel) seed` by
    (gvs[fn_entry_state_def, fn_entry_label_def] >> simp[current_dispatched_cut_def]) >>
  drule current_dispatched_cut_prefix >>
  disch_then (qspecl_then [`eb.bb_label`, `[]`, `CurrentEntry remaining`] mp_tac) >>
  simp[] >> simp[current_dispatched_cut_def] >> metis_tac[]
QED

Theorem current_actual_dispatched_dominator:
  wf_function fn /\ entry_block fn = SOME eb /\ fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
    (SOME (CurrentEntry remaining)) (OK before) before /\ before.vs_prev_bb = SOME p /\
  dominates (dom_analyze (cfg_analyze fn) fn) h p ==>
  ?phis. MEM (CurrentBatch h phis) phases
Proof
  strip_tac >> drule_all current_actual_dispatched_route >> strip_tac >>
  `(\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  `LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls eb.bb_label p` by
    asm_rewrite_tac[] >>
  qspecl_then [`fn`, `eb`, `ls`, `p`] mp_tac dom_on_every_path >>
  asm_rewrite_tac[] >> disch_then (qspec_then `h` mp_tac) >>
  gvs[dominates_def] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem current_first_arrival_exit_token:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
    (SOME (CurrentEntry remaining)) (OK before) before /\
  before.vs_prev_bb = SOME p /\ fn_cfg_edge fn p h /\
  MEM ev events /\ current_event_label ev = p /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  current_event_exit_env ev v <> CurrentInserted v h
Proof
  strip_tac >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_certificate_static_env >> strip_tac >>
  drule_all current_actual_path_chain >> strip_tac >>
  strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) h p` by
    (irule current_exit_inserted_dominates >> simp[] >>
     qexistsl_tac [`current_actual_inserted fn`, `REVERSE path`, `v`, `v`] >>
     gvs[]) >>
  metis_tac[current_actual_dispatched_dominator]
QED

Theorem current_inserted_owner_exit_name[local]:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ first_block_no_preds fn /\
  current_actual_inserted fn v h /\ MEM ev events ==>
  ?V. current_history_valid V H /\
    current_token_name H (current_event_exit_env ev v) =
      SOME (latest_current_name (current_event_exit_rs ev) v)
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  `?old. lookup_block h fn.fn_blocks = SOME old` by
    (gvs[fn_labels_def, MEM_MAP] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       gvs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
  drule_all current_certificate_inserted_prefix >> strip_tac >>
  `MEM (CurrentInserted v h,v) (FLAT (A h))` by
    (simp[current_block_annotations_def, FLAT_APPEND] >>
     metis_tac[current_inserted_annotation_member, lookup_block_label]) >>
  `?hev. MEM hev events /\ current_event_label hev = h` by
    metis_tac[current_certificate_event_at] >>
  `MEM v V` by
    (`current_event_valid A V hev` by metis_tac[EVERY_MEM] >>
     drule current_event_annotation_owner_covered >> simp[] >>
     disch_then (qspecl_then [`v`, `CurrentInserted v h`] mp_tac) >> gvs[]) >>
  qexists_tac `V` >> simp[] >>
  irule (cj 2 current_event_names_accessors) >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_first_arrival_exit_name_residual:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ first_block_no_preds fn /\
  current_actual_inserted fn v h /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  fn_entry_state fn seed /\
  current_actual_prefix fn ctx (CurrentEntry fuel) seed phases
    (SOME (CurrentEntry remaining)) (OK before) before /\
  before.vs_prev_bb = SOME p /\ fn_cfg_edge fn p h /\
  MEM ev events /\ current_event_label ev = p /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  (latest_current_name (current_event_exit_rs ev) v = x <=>
    x = v /\ current_event_exit_env ev v = CurrentDefault v)
Proof
  strip_tac >>
  `current_event_exit_env ev v <> CurrentInserted v h` by
    metis_tac[current_first_arrival_exit_token] >>
  drule_all current_inserted_owner_exit_name >> strip_tac >>
  drule_all current_certificate_static_env >> strip_tac >>
  qpat_x_assum `!v. current_event_exit_env ev v = _`
    (fn th => fs[th]) >>
  drule_all current_exit_name_alias_residual >> simp[]
QED

(* Checkpoint: the first-arrival result is token provenance, not target value
   readiness. current_first_arrival_exit_name_residual retains exactly the
   CurrentDefault v collision with the first allocation's spelling v. No
   demand-to-nondefault lemma or return-epoch/cleanup-alias exclusion is
   established here. The predecessor is an explicit string p, with
   before.vs_prev_bb = SOME p; the earlier RefreshProbe candidate comment
   passing that option directly to fn_cfg_edge is to be read with this
   correction. The operational route projection includes empty PHI batches
   and uses the existing actual_prefix, without any target-execution seed. *)
