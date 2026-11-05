Theory makeSsaCurrentCompletedBatch
Ancestors makeSsaCurrentCompletedOrdinary makeSsaCurrentMixedBatchReady
  makeSsaCurrentPhiOrigins makeSsaCurrentRetainedJoint makeSsaCurrentExecutionHistory
  makeSsaCurrentJointRuntime
  makeSsaCurrentCompletedReinsertion venomExecSemantics venomState venomWf
  list rich_list alist

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
