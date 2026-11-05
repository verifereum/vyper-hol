Theory makeSsaCurrentPostbatchAttribution
Ancestors makeSsaCurrentReinsertionOrder makeSsaCurrentRetainedRead
  makeSsaCurrentRetainedNonclobber makeSsaCurrentRetainedProjection
  makeSsaCurrentRetainedJoint makeSsaCurrentPhiOrigins list arithmetic

Theorem current_certificate_reinserted_selected:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h /\
  fn_phis_non_degenerate fn /\ old.bb_instructions = phis ++ tail /\
  EVERY (\p. p.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  resolve_phi p (EL i old.bb_instructions).inst_operands = SOME (Var u) ==>
  ?out src r c batch.
    lookup_block h fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal h i 0) = SOME src /\ src <> v /\
    r < batch /\ batch <= c /\ c < LENGTH out.bb_instructions /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [src] /\
    (EL c out.bb_instructions).inst_opcode = ASSIGN /\
    (EL c out.bb_instructions).inst_operands = [Var src] /\
    (EL c out.bb_instructions).inst_outputs = [v] /\
    EVERY (\p. p.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (DROP batch out.bb_instructions = [] \/
     (HD (DROP batch out.bb_instructions)).inst_opcode <> PHI) /\
    resolve_phi p (EL r out.bb_instructions).inst_operands =
      SOME (Var (latest_current_name (current_event_exit_rs ev) u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinsertion_order >>
  disch_then (qx_choosel_then [`out`, `src`, `r`, `c`, `batch`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all current_certificate_retained_read >>
  disch_then (qx_choosel_then [`out2`, `r2`, `name`] strip_assume_tac) >>
  `out2 = out /\ name = src` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    metis_tac[current_certificate_block_outputs_distinct] >>
  `r = r2` by
    (irule current_distinct_flat_output_index >>
     qexistsl_tac [`out.bb_instructions`, `name`] >> simp[] >> decide_tac) >>
  qexistsl_tac [`r`, `c`, `batch`] >> simp[]
QED

Theorem current_certificate_reinserted_batch_origin:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h /\
  fn_phis_non_degenerate fn /\ old.bb_instructions = phis ++ tail /\
  EVERY (\p. p.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  resolve_phi p (EL i old.bb_instructions).inst_operands = SOME (Var u) /\
  ALOOKUP N (latest_current_name (current_event_exit_rs ev) u) = SOME origin ==>
  ?out src r c batch.
    lookup_block h fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal h i 0) = SOME src /\ src <> v /\
    r < batch /\ batch <= c /\ c < LENGTH out.bb_instructions /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [src] /\
    (EL c out.bb_instructions).inst_opcode = ASSIGN /\
    (EL c out.bb_instructions).inst_operands = [Var src] /\
    (EL c out.bb_instructions).inst_outputs = [v] /\
    EVERY (\p. p.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (DROP batch out.bb_instructions = [] \/
     (HD (DROP batch out.bb_instructions)).inst_opcode <> PHI) /\
    resolve_phi p (EL r out.bb_instructions).inst_operands =
      SOME (Var (latest_current_name (current_event_exit_rs ev) u)) /\
    current_phi_origin_read N p (EL r out.bb_instructions) (src,origin) /\
    (!bindings. LIST_REL (current_phi_origin_read N p)
      (TAKE batch out.bb_instructions) bindings ==>
      ALOOKUP (bindings ++ N) src = SOME origin)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinserted_selected >>
  disch_then (qx_choosel_then [`out`, `src`, `r`, `c`, `batch`]
    (map_every assume_tac o CONJUNCTS)) >>
  `current_phi_origin_read N p (EL r out.bb_instructions) (src,origin)` by
    (simp[current_phi_origin_read_def] >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    metis_tac[current_certificate_block_outputs_distinct] >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) (TAKE batch out.bb_instructions)))` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     qspec_then `batch` (qspec_then `out.bb_instructions` mp_tac) TAKE_DROP >>
     metis_tac[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  `MEM (EL r out.bb_instructions) (TAKE batch out.bb_instructions)` by
    (simp[MEM_EL] >> qexists `r` >> simp[EL_TAKE] >> decide_tac) >>
  qexistsl_tac [`out`, `src`, `r`, `c`, `batch`] >> simp[] >>
  rpt strip_tac >> irule current_phi_origin_batch_projection >>
  goal_assum $ drule_at Any >> simp[] >>
  qexists `EL r out.bb_instructions` >> simp[]
QED
