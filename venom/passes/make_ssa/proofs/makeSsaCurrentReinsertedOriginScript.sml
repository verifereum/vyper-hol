Theory makeSsaCurrentReinsertedOrigin
Ancestors makeSsaCurrentRetainedNonclobber makeSsaCurrentCleanupOrigins
  makeSsaCurrentReinsertionOrder makeSsaCurrentCleanupRuntime makeSsaCurrentJointRuntime
  makeSsaCurrentSourceCuts makeSsaCurrentAllocation makeSsaCurrentPlacementCut
  venomInst venomWf cfgWf unitShapeDefs makeSsaCurrentDefs list alist option

Theorem current_cleanup_origins_selected_copy:
  !copies k M N.
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) copies)) /\
  k < LENGTH copies /\ (EL k copies).inst_opcode = ASSIGN /\
  (EL k copies).inst_operands = [Var src] /\
  (EL k copies).inst_outputs = [dst] /\
  ~MEM src (FLAT (MAP (\i. i.inst_outputs) copies)) /\
  current_cleanup_origins V copies M = SOME N ==>
  ALOOKUP N dst = ALOOKUP M src /\ IS_SOME (ALOOKUP M src)
Proof
  Induct >> simp[current_cleanup_origins_def] >> rpt gen_tac >>
  Cases_on `k`
  >- (simp[current_cleanup_origins_def] >> strip_tac >>
      gvs[current_cleanup_origin_step_def, AllCaseEqs(), ALL_DISTINCT_APPEND] >>
      `ALOOKUP N dst = ALOOKUP ((dst,origin)::M) dst` by
        (irule current_cleanup_origins_unchanged >>
         qexistsl_tac [`V`, `copies`] >> simp[]) >> simp[]) >>
  simp[] >> strip_tac >> gvs[AllCaseEqs(), ALL_DISTINCT_APPEND] >>
  rename1 `current_cleanup_origin_step V h M = SOME next` >>
  `ALOOKUP next src = ALOOKUP M src` by
    (irule current_cleanup_origin_step_unchanged >>
     qexistsl_tac [`V`, `h`] >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem current_cleanup_segment_selected_copy:
  insts = pre ++ copies ++ rest /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  r < LENGTH pre /\ LENGTH pre <= c /\ c < LENGTH pre + LENGTH copies /\
  (EL r insts).inst_outputs = [src] /\
  (EL c insts).inst_opcode = ASSIGN /\
  (EL c insts).inst_operands = [Var src] /\
  (EL c insts).inst_outputs = [dst] /\
  current_cleanup_origins V copies M = SOME N ==>
  ALOOKUP N dst = ALOOKUP M src /\ IS_SOME (ALOOKUP M src)
Proof
  strip_tac >>
  `MEM src (FLAT (MAP (\i. i.inst_outputs) pre))` by
    (gvs[EL_APPEND_EQN] >> simp[MEM_FLAT, MEM_MAP] >>
     qexists ` [src]` >> simp[] >> metis_tac[EL_MEM]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  irule current_cleanup_origins_selected_copy >>
  qexistsl_tac [`V`, `copies`, `c - LENGTH pre`] >>
  gvs[EL_APPEND_EQN]
QED

Theorem current_certificate_reinserted_origin:
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
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis ==>
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
    (!copies rest V M N.
      out.bb_instructions = TAKE batch out.bb_instructions ++ copies ++ rest /\
      c < batch + LENGTH copies /\ current_cleanup_origins V copies M = SOME N ==>
      ALOOKUP N v = ALOOKUP M src /\ IS_SOME (ALOOKUP M src))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinsertion_order >>
  disch_then (qx_choose_then `out` (qx_choose_then `src`
    (qx_choose_then `r` (qx_choose_then `c` (qx_choose_then `batch`
      (map_every assume_tac o CONJUNCTS)))))) >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    (irule current_certificate_block_outputs_distinct >> metis_tac[]) >>
  qexistsl_tac [`out`, `src`, `r`, `c`, `batch`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `LENGTH (TAKE batch out.bb_instructions) = batch` by simp[] >>
  irule current_cleanup_segment_selected_copy >>
  goal_assum $ drule_at Any >>
  qexistsl_tac [`c`, `out.bb_instructions`, `TAKE batch out.bb_instructions`, `r`, `rest`] >>
  simp[]
QED

Theorem current_cleanup_segment_runtime_origin:
  insts = pre ++ copies ++ rest /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  r < LENGTH pre /\ LENGTH pre <= c /\ c < LENGTH pre + LENGTH copies /\
  (EL r insts).inst_outputs = [src] /\
  (EL c insts).inst_opcode = ASSIGN /\
  (EL c insts).inst_operands = [Var src] /\
  (EL c insts).inst_outputs = [dst] /\
  EVERY current_cleanup_shape copies /\ current_origin_realizes V M after_phi /\
  current_copies_run copies after_phi = OK ready ==>
  ?N. current_cleanup_origins V copies M = SOME N /\
    current_origin_realizes V N ready /\
    ALOOKUP N dst = ALOOKUP M src /\ IS_SOME (ALOOKUP M src) /\
    lookup_var dst ready = lookup_var src after_phi
Proof
  strip_tac >> drule_all current_cleanup_origins_reflect >> strip_tac >>
  drule_all current_cleanup_segment_selected_copy >> strip_tac >>
  qexists `N` >> simp[] >> fs[current_origin_realizes_def]
QED

Theorem current_certificate_reinserted_runtime_origin:
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
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis ==>
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
    (!copies rest V M after_phi ready.
      out.bb_instructions = TAKE batch out.bb_instructions ++ copies ++ rest /\
      c < batch + LENGTH copies /\ EVERY current_cleanup_shape copies /\
      current_origin_realizes V M after_phi /\
      current_copies_run copies after_phi = OK ready ==>
      ?N. current_cleanup_origins V copies M = SOME N /\
        current_origin_realizes V N ready /\
        ALOOKUP N v = ALOOKUP M src /\ IS_SOME (ALOOKUP M src) /\
        lookup_var v ready = lookup_var src after_phi)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinserted_origin >>
  disch_then (qx_choose_then `out` (qx_choose_then `src`
    (qx_choose_then `r` (qx_choose_then `c` (qx_choose_then `batch`
      (map_every assume_tac o CONJUNCTS)))))) >>
  qexistsl_tac [`out`, `src`, `r`, `c`, `batch`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all current_cleanup_origins_reflect >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists `N` >> simp[] >> fs[current_origin_realizes_def]
QED
