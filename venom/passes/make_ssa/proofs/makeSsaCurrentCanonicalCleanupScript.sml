Theory makeSsaCurrentCanonicalCleanup
Ancestors makeSsaCurrentPhaseShape makeSsaCurrentCleanupCopyOrigin
  makeSsaCurrentCleanupRuntime makeSsaCurrentStaticCuts
  makeSsaCurrentStaticDemandProbe makeSsaCurrentCompletedBatch
  makeSsaCurrentCleanupShape makeSsaCurrentInsertedValue makeSsaCurrentDefs venomExecSemantics venomInst list rich_list

Theorem current_graph_cleanup_cut:
  current_graph_predecessor fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  a = phi_prefix_length old.bb_instructions /\
  phi_prefix_length out.bb_instructions <= j /\
  j <= current_static_body_start old.bb_instructions out.bb_instructions ==>
  current_graph_admissible fn fn' (CurrentStaticCut p h a j)
Proof
  simp[current_graph_admissible_def] >> metis_tac[]
QED

Theorem current_graph_cleanup_edge:
  current_graph_predecessor fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  a = phi_prefix_length old.bb_instructions /\
  phi_prefix_length out.bb_instructions <= j /\
  j < current_static_body_start old.bb_instructions out.bb_instructions ==>
  current_graph_edge fn fn' (CurrentStaticCut p h a j)
    (CurrentStaticCut p h a (SUC j)) 1
Proof
  strip_tac >> rewrite_tac[current_graph_edge_def] >> conj_tac
  >- (simp[current_static_edge_def] >> metis_tac[]) >>
  conj_tac >> irule current_graph_cleanup_cut >>
  goal_assum $ drule_at Any >> simp[] >> decide_tac
QED

Theorem current_collapsed_phi_cleanup_shape:
  inst.inst_opcode = PHI /\ (simplify_current_phi inst).inst_opcode <> PHI ==>
  current_cleanup_shape (simplify_current_phi inst)
Proof
  strip_tac >>
  gvs[simplify_current_phi_def, keep_current_phi_vars_def] >>
  Cases_on `EVERY (\v. MEM v (inst_ir_vars inst)) (inst_ir_vars (simplify_current_phi_raw inst))` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[simplify_current_phi_raw_def, current_phi_output_def] >>
  Cases_on `t` >> gvs[current_phi_output_def] >>
  Cases_on `current_phi_values (remove_current_phi_self h inst.inst_operands)` >> gvs[] >>
  Cases_on `x` >> gvs[current_cleanup_shape_def] >>
  Cases_on `EVERY (\w. w = h') t` >> gvs[current_cleanup_shape_def]
QED

Theorem current_no_id_phi_prefix:
  !xs. phi_prefix_length (MAP current_inst_no_id xs) = phi_prefix_length xs
Proof
  Induct >> simp[phi_prefix_length_def, current_inst_no_id_def]
QED

Theorem current_no_id_cleanup_shape:
  current_inst_no_id a = current_inst_no_id b ==>
  (current_cleanup_shape a <=> current_cleanup_shape b)
Proof
  simp[current_inst_no_id_def, instruction_component_equality, current_cleanup_shape_def]
QED

Theorem current_cleanup_prefix_interval:
  EVERY (\i. i.inst_opcode = PHI) pp /\ (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
  out = simplify_current_phi_prefix (pp ++ tt) /\
  k = LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) /\
  m = LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) ==>
  phi_prefix_length out = k /\ k + m = LENGTH pp /\
  LENGTH out = LENGTH pp + LENGTH tt /\
  EVERY current_cleanup_shape (TAKE m (DROP k out))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `k + m = LENGTH pp` by metis_tac[current_cleanup_partition_length, LENGTH_MAP] >>
  `LENGTH out = LENGTH pp + LENGTH tt` by simp[current_cleanup_length] >>
  `EVERY current_cleanup_shape (TAKE m (DROP k out))` by
    (pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `out = _` SUBST_ALL_TAC >>
     drule_all current_cleanup_copy_inverse >> strip_tac >>
     `original.inst_opcode = PHI` by (gvs[EVERY_MEM] >> metis_tac[]) >>
     drule_all current_collapsed_phi_cleanup_shape >>
     metis_tac[current_no_id_cleanup_shape]) >>
  simp[] >>
  drule_all current_cleanup_partition_no_id >>
  disch_then (mp_tac o Q.AP_TERM `phi_prefix_length`) >>
  simp[current_no_id_phi_prefix] >> disch_then SUBST1_TAC >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule current_phi_prefix_maximal_length >>
  simp[EVERY_FILTER, EVERY_MEM] >>
  qmatch_goalsub_abbrev_tac `HD (copies ++ tt)` >>
  `EVERY (\i. i.inst_opcode <> PHI) copies` by
    simp[Abbr `copies`, EVERY_FILTER, EVERY_MEM] >>
  Cases_on `copies` >> gvs[]
QED

Theorem current_cleanup_if_interval:
  lookup_block h renamed = SOME final /\ final.bb_instructions = pp ++ tt /\
  EVERY (\i. i.inst_opcode = PHI) pp /\ (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
  k = (if enabled then LENGTH (FILTER (\i. i.inst_opcode = PHI)
    (MAP simplify_current_phi pp)) else LENGTH pp) /\
  m = (if enabled then LENGTH (FILTER (\i. i.inst_opcode <> PHI)
    (MAP simplify_current_phi pp)) else 0) ==>
  ?out. lookup_block h (simplify_current_phis_if enabled renamed) = SOME out /\
    phi_prefix_length out.bb_instructions = k /\ k + m = LENGTH pp /\
    LENGTH out.bb_instructions = LENGTH pp + LENGTH tt /\
    EVERY current_cleanup_shape (TAKE m (DROP k out.bb_instructions))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[current_cleanup_if_lookup] >> Cases_on `enabled` >> gvs[]
  >- (` (simplify_current_phi_block final).bb_instructions =
         simplify_current_phi_prefix (pp ++ tt)` by
        (irule current_cleanup_block_prefix_eq >> metis_tac[]) >>
      `EVERY (\i. i.inst_opcode = PHI) pp /\
       (tt = [] \/ (HD tt).inst_opcode <> PHI)` by metis_tac[] >>
      drule current_cleanup_prefix_interval >>
      simp[] >> disch_then (qspec_then `tt` mp_tac) >> simp[]) >>
  irule current_phi_prefix_maximal_length >> metis_tac[]
QED

Theorem current_cleanup_interval_index:
  k + m <= LENGTH xs /\ EVERY current_cleanup_shape (TAKE m (DROP k xs)) /\
  k <= j /\ j < k + m ==>
  current_cleanup_shape (EL j xs)
Proof
  strip_tac >>
  `j - k < LENGTH (TAKE m (DROP k xs))` by simp[] >>
  `EL (j-k) (TAKE m (DROP k xs)) = EL j xs` by
    (simp[EL_TAKE, EL_DROP] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  fs[EVERY_EL] >> first_x_assum (qspec_then `j-k` mp_tac) >> simp[]
QED

Theorem current_certificate_cleanup_interval:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  a = phi_prefix_length old.bb_instructions /\
  b = phi_prefix_length out.bb_instructions /\
  e = current_static_body_start old.bb_instructions out.bb_instructions ==>
  b <= e /\ e <= LENGTH out.bb_instructions /\
  EVERY current_cleanup_shape (TAKE (e-b) (DROP b out.bb_instructions)) /\
  ?renamed final pp tt.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\ final.bb_instructions = pp ++ tt /\
    EVERY (\i. i.inst_opcode = PHI) pp /\ (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
    LENGTH tt = LENGTH old.bb_instructions - a /\ e = LENGTH pp /\
    b = (if blocks_have_leading_phi fn.fn_blocks then
      LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) else LENGTH pp) /\
    e-b = (if blocks_have_leading_phi fn.fn_blocks then
      LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) else 0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspec_then `old.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  `a = LENGTH (collect_phis old.bb_instructions)` by
    metis_tac[current_phi_prefix_maximal_length] >>
  drule_all current_certificate_phase_blocks >>
  disch_then (qx_choose_then `pre` (qx_choose_then `renamed`
    (qx_choose_then `final` (qx_choose_then `pp` (qx_choose_then `tt`
      (qx_choose_then `out0` (map_every assume_tac o CONJUNCTS))))))) >>
  qpat_x_assum `current_phi_view _ = _` kall_tac >>
  qpat_x_assum `!v. current_actual_inserted _ _ _ <=> _` kall_tac >>
  qpat_x_assum `!k v. _ ==> _` kall_tac >>
  qpat_x_assum `!i v. _ ==> _` kall_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` kall_tac >>
  `?out. lookup_block h (simplify_current_phis_if
      (blocks_have_leading_phi fn.fn_blocks) renamed) = SOME out /\
    phi_prefix_length out.bb_instructions =
      (if blocks_have_leading_phi fn.fn_blocks then
        LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) else LENGTH pp) /\
    (if blocks_have_leading_phi fn.fn_blocks then
        LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) else LENGTH pp) +
      (if blocks_have_leading_phi fn.fn_blocks then
        LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) else 0) = LENGTH pp /\
    LENGTH out.bb_instructions = LENGTH pp + LENGTH tt /\
    EVERY current_cleanup_shape (TAKE
      (if blocks_have_leading_phi fn.fn_blocks then
        LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp)) else 0)
      (DROP (if blocks_have_leading_phi fn.fn_blocks then
        LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) else LENGTH pp)
        out.bb_instructions))` by
    (irule current_cleanup_if_interval >> simp[] >> metis_tac[]) >>
  `out0 = out` by metis_tac[optionTheory.SOME_11] >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >>
  `LENGTH tt = LENGTH old.bb_instructions - a` by simp[] >>
  `e = LENGTH pp` by
    (gvs[current_static_body_start_def] >> decide_tac) >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks` >> gvs[]
  >- (`current_static_body_start old.bb_instructions out.bb_instructions -
       LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) =
       LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pp))`
       by decide_tac >>
      pop_assum (fn th => rewrite_tac[th]) >>
      simp[] >> qexistsl_tac [`renamed`, `final`, `pp`, `tt`] >> simp[]) >>
  qexistsl_tac [`renamed`, `final`, `pp`, `tt`] >> simp[]
QED

Theorem current_certificate_cleanup_edges:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  current_graph_predecessor fn p h /\
  a = phi_prefix_length old.bb_instructions /\
  b = phi_prefix_length out.bb_instructions /\
  e = current_static_body_start old.bb_instructions out.bb_instructions ==>
  b <= e /\ e <= LENGTH out.bb_instructions /\
  (!j. b <= j /\ j <= e ==>
    current_graph_admissible fn fn' (CurrentStaticCut p h a j)) /\
  (!j. b <= j /\ j < e ==>
    current_cleanup_shape (EL j out.bb_instructions) /\
    current_graph_edge fn fn' (CurrentStaticCut p h a j)
      (CurrentStaticCut p h a (SUC j)) 1)
Proof
  strip_tac >> drule_all current_certificate_cleanup_interval >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule current_graph_cleanup_cut >> metis_tac[]) >>
  rpt strip_tac
  >- (irule current_cleanup_interval_index >>
      qexistsl_tac [`b`, `e-b`] >> simp[] >> decide_tac) >>
  irule current_graph_cleanup_edge >> metis_tac[]
QED
