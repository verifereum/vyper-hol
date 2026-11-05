Theory makeSsaCurrentCompletedBatch
Ancestors makeSsaCurrentCompletedOrdinary makeSsaCurrentMixedBatchReady
  makeSsaCurrentPhiOrigins makeSsaCurrentRetainedJoint makeSsaCurrentExecutionHistory
  makeSsaCurrentJointRuntime
  makeSsaCurrentCompletedReinsertion venomExecSemantics venomState venomWf
  list rich_list alist cfgHelpers venomExecProps

Theorem current_phi_origin_read_below:
  current_phi_origin_read N p inst (name,origin) /\ current_map_below a N ==>
  FST origin < a
Proof
  rw[current_phi_origin_read_def, current_map_below_def] >>
  metis_tac[ALOOKUP_MEM]
QED

Theorem current_phi_bindings_below:
  !prefix bindings. LIST_REL (current_phi_origin_read N p) prefix bindings /\
    current_map_below a N ==> current_map_below a (bindings ++ N)
Proof
  Induct >> Cases_on `bindings` >> simp[] >> rpt strip_tac >>
  gvs[] >> rename1 `current_phi_origin_read N p inst binding` >>
  PairCases_on `binding` >>
  drule_all current_phi_origin_read_below >> strip_tac >>
  first_x_assum drule_all >> simp[current_map_below_def] >> metis_tac[]
QED

Theorem current_actual_dispatch_continue:
  current_actual_prefix fn C loc seed phases (SOME (CurrentEntry (SUC fuel))) (OK st) st /\
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis st bb.bb_instructions = OK post ==>
  current_actual_prefix fn C loc seed
    (phases ++ [CurrentBatch st.vs_current_bb
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions); CurrentControl])
    (SOME (CurrentBody fuel bb))
    (OK (post with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> drule current_actual_prefix_append >> disch_then irule >> simp[] >>
  irule (cj 2 current_actual_prefix_rules) >>
  irule (cj 1 current_execution_edge_rules) >> simp[]
QED

Theorem current_phi_prefix_maximal_length:
  !pre tail. EVERY (\inst. inst.inst_opcode = PHI) pre /\
    (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
    phi_prefix_length (pre ++ tail) = LENGTH pre
Proof
  Induct >- (Cases >> simp[phi_prefix_length_def]) >>
  rpt strip_tac >> gvs[phi_prefix_length_def] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem current_bounded_batch_continue:
  bb.bb_instructions = prefix ++ suffix /\
  EVERY (\inst. inst.inst_opcode = PHI /\ inst_wf inst) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  st.vs_prev_bb = SOME p /\ current_origin_realizes V N st /\ current_map_below a N /\
  current_actual_prefix fn C loc seed phases (SOME (CurrentEntry (SUC fuel))) (OK st) st /\
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis st bb.bb_instructions = OK post ==>
  ?bindings. LIST_REL (current_phi_origin_read N p) prefix bindings /\
    EVERY (\b. IS_SOME (V (SND b))) bindings /\
    current_origin_realizes V (bindings ++ N) post /\
    current_origin_realizes V (bindings ++ N) (post with vs_inst_idx := LENGTH prefix) /\
    current_map_below a (bindings ++ N) /\
    execution_frame post = execution_frame st /\
    post.vs_current_bb = st.vs_current_bb /\ post.vs_prev_bb = st.vs_prev_bb /\
    current_actual_prefix fn C loc seed
      (phases ++ [CurrentBatch st.vs_current_bb prefix; CurrentControl])
      (SOME (CurrentBody fuel bb))
      (OK (post with vs_inst_idx := LENGTH prefix)) (post with vs_inst_idx := LENGTH prefix) /\
    (!inst name origin. ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) prefix)) /\
      MEM inst prefix /\ current_phi_origin_read N p inst (name,origin) ==>
      ALOOKUP (bindings ++ N) name = SOME origin /\ lookup_var name post = V origin)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_phis st (prefix ++ suffix) = OK post` by metis_tac[] >>
  drule_all current_eval_phis_origin_batch >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI) prefix` by fs[EVERY_MEM] >>
  `phi_prefix_length bb.bb_instructions = LENGTH prefix` by
    metis_tac[current_phi_prefix_maximal_length] >>
  `TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions = prefix` by
    gvs[TAKE_APPEND] >>
  `current_map_below a (bindings ++ N)` by metis_tac[current_phi_bindings_below] >>
  qexists `bindings` >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- fs[current_origin_realizes_def, lookup_var_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[current_actual_dispatch_continue] >>
  rpt strip_tac >>
  `ALOOKUP (bindings ++ N) name = SOME origin` by
    metis_tac[current_phi_origin_batch_projection] >>
  fs[current_origin_realizes_def]
QED

Theorem current_certificate_mixed_dispatch_continue:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  first_block_no_preds fn /\ blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  fn_phi_outputs_single_def fn /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pred /\
  st.vs_prev_bb = SOME p /\ st'.vs_prev_bb = SOME p /\
  st.vs_current_bb = h /\ st'.vs_current_bb = h /\
  current_singleton_agree (current_instruction_singleton_table fn H) st st' /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = target_phis ++ target_tail /\
  EVERY (\j. j.inst_opcode = PHI) target_phis /\
  (target_tail = [] \/ (HD target_tail).inst_opcode <> PHI) /\
  eval_phis st phis = OK post /\
  (!v n. current_actual_inserted fn v h /\
    current_token_name H (CurrentInserted v h) = SOME n /\
    MEM n (FLAT (MAP (\j. j.inst_outputs) target_phis)) ==>
    current_name_agree (current_event_exit_rs ev) [v] st st' /\
    ?value. lookup_var v st = SOME value) /\
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  current_map_below a M /\ current_map_below a N /\ current_archive_valid a V archive /\
  current_actual_prefix fn C loc seed phases (SOME (CurrentEntry (SUC fuel))) (OK st) st /\
  current_actual_prefix fn' C' loc' seed' phases' (SOME (CurrentEntry (SUC fuel'))) (OK st') st' ==>
  ?post' bindings bindings'.
    eval_phis st' target_phis = OK post' /\
    current_singleton_agree (current_instruction_singleton_table fn H) post post' /\
    current_singleton_agree (current_instruction_singleton_table fn H)
      (post with vs_inst_idx := LENGTH phis) (post' with vs_inst_idx := LENGTH target_phis) /\
    LIST_REL (current_phi_origin_read M p) phis bindings /\
    LIST_REL (current_phi_origin_read N p) target_phis bindings' /\
    EVERY (\b. IS_SOME (V (SND b))) bindings /\
    EVERY (\b. IS_SOME (V (SND b))) bindings' /\
    current_origin_realizes V (bindings ++ M) post /\
    current_origin_realizes V (bindings' ++ N) post' /\
    current_origin_realizes V (bindings ++ M) (post with vs_inst_idx := LENGTH phis) /\
    current_origin_realizes V (bindings' ++ N) (post' with vs_inst_idx := LENGTH target_phis) /\
    current_map_below a (bindings ++ M) /\ current_map_below a (bindings' ++ N) /\
    current_archive_valid a V archive /\
    execution_frame post = execution_frame st /\ execution_frame post' = execution_frame st' /\
    post.vs_current_bb = h /\ post'.vs_current_bb = h /\
    post.vs_prev_bb = SOME p /\ post'.vs_prev_bb = SOME p /\
    current_actual_prefix fn C loc seed
      (phases ++ [CurrentBatch h phis; CurrentControl])
      (SOME (CurrentBody fuel old))
      (OK (post with vs_inst_idx := LENGTH phis)) (post with vs_inst_idx := LENGTH phis) /\
    current_actual_prefix fn' C' loc' seed'
      (phases' ++ [CurrentBatch h target_phis; CurrentControl])
      (SOME (CurrentBody fuel' out))
      (OK (post' with vs_inst_idx := LENGTH target_phis)) (post' with vs_inst_idx := LENGTH target_phis) /\
    (!inst name origin. ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) phis)) /\
      MEM inst phis /\ current_phi_origin_read M p inst (name,origin) ==>
      ALOOKUP (bindings ++ M) name = SOME origin /\ lookup_var name post = V origin) /\
    (!inst name origin. ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) target_phis)) /\
      MEM inst target_phis /\ current_phi_origin_read N p inst (name,origin) ==>
      ALOOKUP (bindings' ++ N) name = SOME origin /\ lookup_var name post' = V origin)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_target_phi_prefix_wf >> strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI /\ inst_wf inst) phis` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> rpt strip_tac >>
     metis_tac[lookup_block_MEM, MEM_APPEND]) >>
  drule_all current_certificate_mixed_batch_ready >> strip_tac >>
  `eval_phis st old.bb_instructions = OK post` by
    metis_tac[current_eval_phis_maximal_append] >>
  `eval_phis st' out.bb_instructions = OK post'` by
    metis_tac[current_eval_phis_maximal_append] >>
  `lookup_block st.vs_current_bb fn.fn_blocks = SOME old /\
   lookup_block st'.vs_current_bb fn'.fn_blocks = SOME out` by metis_tac[] >>
  qpat_assum `current_actual_prefix fn C loc seed phases _ _ _`
    (mp_then Any drule_all current_bounded_batch_continue) >>
  disch_then (qx_choose_then `bindings` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `current_actual_prefix fn' C' loc' seed' phases' _ _ _`
    (mp_then Any drule_all current_bounded_batch_continue) >>
  disch_then (qx_choose_then `bindings'` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`post'`, `bindings`, `bindings'`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (irule current_singleton_agree_indices >> first_assum ACCEPT_TAC) >>
  pure_asm_rewrite_tac [] >> rewrite_tac [] >>
  conj_tac
  >- (qpat_x_assum `current_actual_prefix fn C loc seed (_ ++ _) _ _ _` mp_tac >>
      asm_rewrite_tac []) >>
  qpat_x_assum `current_actual_prefix fn' C' loc' seed' (_ ++ _) _ _ _` mp_tac >>
  asm_rewrite_tac []
QED
