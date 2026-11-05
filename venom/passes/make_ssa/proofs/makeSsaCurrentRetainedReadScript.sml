Theory makeSsaCurrentRetainedRead
Ancestors makeSsaCurrentReinsertionSlots makeSsaCurrentPhiRuntime
  makeSsaCurrentFinalSlots makeSsaCurrentAnalysis makeSsaCurrentDefs venomExecProps
  makeSsaCurrentPhaseShape makeSsaCurrentRetainedNonclobber
  makeSsaCurrentCleanupShape makeSsaCurrentCleanupBoundary makeSsaCurrentReinsertionOrder
  venomInst venomWf cfgWf list rich_list option pair

Theorem current_find_map_preserved_fst:
  !slots. (!slot. FST (f slot) = FST slot) ==>
  FIND (\slot. FST slot = p) (MAP f slots) =
    OPTION_MAP f (FIND (\slot. FST slot = p) slots)
Proof
  Induct >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `FST h = p` >> simp[]
QED

Theorem current_event_fold_selected_slot:
  ALL_DISTINCT (MAP current_event_label events) /\ MEM ev events /\
  current_event_label ev = p /\
  MEM h (case ALOOKUP sm p of NONE => [] | SOME ss => ss) /\
  resolve_phi p (current_phi_slots slots) = SOME (Var v) ==>
  resolve_phi p
    (FOLDL (\ops ev. current_event_operand_action sm h ev ops)
      (current_phi_slots slots) events) =
    SOME (Var (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >> rewrite_tac[current_event_fold_slots, current_resolve_phi_slots] >>
  simp[current_find_map_preserved_fst] >>
  gvs[current_resolve_phi_slots, AllCaseEqs()] >>
  rename1 `FIND _ slots = SOME slot` >>
  `FST slot = current_event_label ev` by (drule FIND_P >> simp[]) >>
  drule_all current_event_fold_pair_unique >> simp[]
QED

Theorem current_certificate_retained_read_replay:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [dst] /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  resolve_phi p (EL i old.bb_instructions).inst_operands = SOME (Var v) ==>
  ?pre renamed final name.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\
    EVERY (\inst. inst.inst_opcode = PHI) pre /\
    current_phi_view final.bb_instructions =
      FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
        (current_phi_view (pre ++ old.bb_instructions)) events /\
    LENGTH pre + i < LENGTH final.bb_instructions /\
    (EL (LENGTH pre + i) final.bb_instructions).inst_opcode = PHI /\
    (EL (LENGTH pre + i) final.bb_instructions).inst_outputs = [name] /\
    current_token_name H (CurrentOriginal h i 0) = SOME name /\
    simplify_current_phi (EL (LENGTH pre + i) final.bb_instructions) =
      EL (LENGTH pre + i) final.bb_instructions /\
    resolve_phi p (EL (LENGTH pre + i) final.bb_instructions).inst_operands =
      SOME (Var (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >> drule_all current_certificate_block_replay >> strip_tac >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def] >> first_x_assum irule >> qexists `old` >>
     conj_tac >- metis_tac[lookup_block_MEM] >> metis_tac[EL_MEM]) >>
  `phi_well_formed (EL i old.bb_instructions).inst_operands` by
    (qpat_x_assum `inst_wf _` (mp_tac o REWRITE_RULE [inst_wf_def]) >>
     qpat_x_assum `_.inst_opcode = PHI` (fn th => rewrite_tac[th]) >> simp[]) >>
  drule current_wf_phi_slots >> strip_tac >>
  `LENGTH pre + i < LENGTH (pre ++ old.bb_instructions) /\
   (EL (LENGTH pre + i) (pre ++ old.bb_instructions)).inst_opcode = PHI` by
    simp[EL_APPEND_EQN] >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_certificate_event_labels_distinct] >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `resolve_phi p (EL (LENGTH pre + i) final.bb_instructions).inst_operands =
      SOME (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (gvs[EL_APPEND_EQN] >>
     qpat_assum `_.inst_operands = current_phi_slots _`
       (fn th => once_rewrite_tac[th]) >>
     irule current_event_fold_selected_slot >>
     goal_assum $ drule_at Any >> simp[] >> metis_tac[]) >>
  `EVERY (\inst. inst.inst_opcode = PHI) pre` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> simp[build_phi_inst_supply_def]) >>
  first_x_assum (qspecl_then [`i`, `dst`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`pre`, `renamed`, `final`, `src`] >> fs[arithmeticTheory.ADD_COMM]
QED

Theorem current_cleanup_parts_retained_member:
  !insts phis ordinary.
  simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
  MEM inst insts /\ simplify_current_phi inst = inst ==>
  MEM inst (phis ++ ordinary)
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[] >> pairarg_tac >> gvs[] >>
      Cases_on `(simplify_current_phi h).inst_opcode = PHI` >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[MEM_APPEND]) >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem current_cleanup_block_retained_member:
  MEM inst bb.bb_instructions /\ simplify_current_phi inst = inst ==>
  MEM (current_inst_no_id inst)
    (MAP current_inst_no_id (simplify_current_phi_block bb).bb_instructions)
Proof
  strip_tac >> Cases_on `bb.bb_instructions`
  >- gvs[] >>
  simp[simplify_current_phi_block_def] >> IF_CASES_TAC
  >- (simp[simplify_current_phi_prefix_def] >> pairarg_tac >> fs[] >>
      `MEM inst (phis ++ ordinary)` by
        (irule current_cleanup_parts_retained_member >> simp[] >>
         qexists `h::t` >> simp[]) >>
      `LENGTH (MAP (\i. i.inst_id) (h::t)) = LENGTH (phis ++ ordinary)` by
        (drule simplify_current_phi_prefix_parts_length >> simp[]) >>
      drule current_reassign_no_id >> simp[] >> disch_then SUBST1_TAC >>
      simp[MEM_MAP] >> metis_tac[MEM_APPEND]) >>
  simp[MEM_MAP] >> qexists `inst` >> fs[]
QED

Theorem current_certificate_retained_read:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [dst] /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  resolve_phi p (EL i old.bb_instructions).inst_operands = SOME (Var v) ==>
  ?out r name. lookup_block h fn'.fn_blocks = SOME out /\
    r < LENGTH out.bb_instructions /\ (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [name] /\
    current_token_name H (CurrentOriginal h i 0) = SOME name /\
    resolve_phi p (EL r out.bb_instructions).inst_operands =
      SOME (Var (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >> drule_all current_certificate_retained_read_replay >> strip_tac >>
  `MEM (current_inst_no_id (EL (LENGTH pre + i) final.bb_instructions))
    (MAP current_inst_no_id
      (if blocks_have_leading_phi fn.fn_blocks then simplify_current_phi_block final
       else final).bb_instructions)` by
    (Cases_on `blocks_have_leading_phi fn.fn_blocks` >> simp[]
     >- (irule current_cleanup_block_retained_member >>
         fs[arithmeticTheory.ADD_COMM] >> metis_tac[EL_MEM]) >>
     simp[MEM_MAP] >> qexists `EL (LENGTH pre + i) final.bb_instructions` >>
     fs[arithmeticTheory.ADD_COMM] >> metis_tac[EL_MEM]) >>
  `lookup_block h fn'.fn_blocks = SOME
    (if blocks_have_leading_phi fn.fn_blocks then simplify_current_phi_block final
     else final)` by simp[current_cleanup_if_lookup] >>
  qmatch_asmsub_abbrev_tac `lookup_block h fn'.fn_blocks = SOME out` >>
  qpat_x_assum `MEM _ (MAP _ _)` mp_tac >>
  simp[MEM_MAP, MEM_EL] >> strip_tac >>
  qexists `n` >>
  imp_res_tac current_no_id_fields >> gvs[arithmeticTheory.ADD_COMM]
QED

Theorem current_replay_retained_leading_position:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\ final.bb_instructions = pp ++ tt /\
  EVERY (\j. j.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) /\ k < LENGTH pp /\
  simplify_current_phi (EL k pp) = EL k pp ==>
  ?out r batch. lookup_block h fn'.fn_blocks = SOME out /\
    r < batch /\ batch <= LENGTH out.bb_instructions /\
    current_inst_no_id (EL r out.bb_instructions) = current_inst_no_id (EL k pp) /\
    EVERY (\j. j.inst_opcode = PHI) (TAKE batch out.bb_instructions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?out. lookup_block h fn'.fn_blocks = SOME out` by
    simp[current_cleanup_if_lookup] >>
  drule_all current_phase_retained_position >> strip_tac >>
  Cases_on `enabled` >> fs[EL_APPEND_EQN]
  >- (`pp <> []` by (Cases_on `pp` >> gvs[]) >>
      `out.bb_instructions = simplify_current_phi_prefix (pp ++ tt)` by
        (gvs[current_cleanup_if_lookup] >> Cases_on `pp` >- gvs[] >>
         gvs[EVERY_DEF] >> simp[simplify_current_phi_block_def]) >>
      qexistsl_tac [`current_cleanup_occurrence_rank pp k`,
        `LENGTH (FILTER (\j. j.inst_opcode = PHI) (MAP simplify_current_phi pp))`] >>
      simp[] >> conj_tac
      >- (simp[current_cleanup_length] >>
          mp_tac (Q.SPEC `MAP simplify_current_phi pp` current_cleanup_partition_length) >>
          simp[]) >>
      simp[EL_APPEND_EQN] >>
      irule (cj 1 current_cleanup_batch_boundary) >> simp[]) >>
  qexistsl_tac [`k`, `LENGTH pp`] >>
  gvs[current_cleanup_if_lookup, EL_APPEND_EQN, TAKE_APPEND]
QED

Theorem current_certificate_retained_leading_read:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [dst] /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  resolve_phi p (EL i old.bb_instructions).inst_operands = SOME (Var v) ==>
  ?out r batch name. lookup_block h fn'.fn_blocks = SOME out /\
    r < batch /\ batch <= LENGTH out.bb_instructions /\
    EVERY (\j. j.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [name] /\
    current_token_name H (CurrentOriginal h i 0) = SOME name /\
    resolve_phi p (EL r out.bb_instructions).inst_operands =
      SOME (Var (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >>
  `i < LENGTH old.bb_instructions` by simp[] >>
  drule_all current_certificate_retained_read_replay >> strip_tac >>
  `?pp tt. final.bb_instructions = pp ++ tt /\
    LENGTH pp = LENGTH (pre ++ phis) /\ LENGTH tt = LENGTH tail /\
    EVERY (\j. j.inst_opcode = PHI) pp /\
    (tt = [] \/ (HD tt).inst_opcode <> PHI)` by
    (qpat_assum `current_phi_view _ = _` mp_tac >>
     qpat_assum `old.bb_instructions = _`
       (fn th => pure_rewrite_tac[th, APPEND_ASSOC]) >>
     disch_then (mp_then Any mp_tac
       (Q.INST [`pre` |-> `pre ++ phis`, `tail` |-> `tail`]
         current_replay_phase_split)) >>
     simp[EVERY_APPEND]) >>
  `LENGTH pre + i < LENGTH pp` by simp[] >>
  `simplify_current_phi (EL (LENGTH pre + i) pp) = EL (LENGTH pre + i) pp` by
    fs[EL_APPEND_EQN] >>
  drule current_replay_retained_leading_position >>
  disch_then (qspecl_then [`tt`, `pp`, `LENGTH pre + i`, `h`, `final`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`out`, `r`, `batch`] >> simp[] >>
  imp_res_tac current_no_id_fields >> fs[EL_APPEND_EQN, arithmeticTheory.ADD_COMM]
QED
