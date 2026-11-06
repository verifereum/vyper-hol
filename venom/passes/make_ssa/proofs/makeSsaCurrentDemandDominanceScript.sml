Theory makeSsaCurrentDemandDominance
Ancestors
  makeSsaCurrentDemand makeSsaCurrentAvailability makeSsaCurrentOccurrence venomExecProofs
Libs
  listTheory arithmeticTheory venomWfTheory

Theorem current_live_post_phi_available:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  i <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) l i) ==>
  current_available fn v l i
Proof
  metis_tac[current_live_post_phi_demand, current_demand_available]
QED

Theorem current_available_definition:
  fn_reachable fn l /\ current_available fn v l i ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
          MEM v di.inst_outputs
Proof
  simp[fn_reachable_def, current_available_def] >> rpt strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  qpat_x_assum `!path. _` (qspec_then `path` mp_tac) >>
  simp[] >> strip_tac >- metis_tac[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    (irule EL_MEM >> decide_tac) >> metis_tac[]
QED

Theorem current_available_unique_dominates:
  fn_reachable fn l /\ current_available fn v l i /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  fn_dominates fn db.bb_label l
Proof
  simp[current_available_def, fn_dominates_def] >> rpt strip_tac >>
  qpat_x_assum `!path. _` (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (`db = db'` by metis_tac[current_single_def_occurrence] >>
      gvs[] >> irule EL_MEM >> decide_tac) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    (irule EL_MEM >> decide_tac) >>
  `db = bb` by metis_tac[current_single_def_occurrence] >>
  gvs[] >>
  `bb.bb_label = LAST path` by metis_tac[lookup_block_label] >>
  Cases_on `path` using SNOC_CASES >> gvs[]
QED

Theorem current_available_local_index:
  wf_function fn /\ fn_reachable fn l /\ current_available fn v l i /\
  lookup_block l fn.fn_blocks = SOME bb /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM di bb.bb_instructions /\ MEM v di.inst_outputs ==>
  ?j. j < i /\ MEM v (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  fs[fn_reachable_def] >> drule rtc_to_fn_path >> strip_tac >>
  drule_all current_path_first_target >> strip_tac >>
  qpat_x_assum `current_available _ _ _ _` mp_tac >>
  simp[current_available_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `!path. _` (qspec_then `pre ++ [LAST path]` mp_tac) >>
  simp[] >> reverse strip_tac >- metis_tac[] >>
  `db = bb` by metis_tac[current_single_def_occurrence] >>
  gvs[] >>
  `k < LENGTH pre` by decide_tac >>
  `EL k (pre ++ [LAST path]) = EL k pre` by simp[EL_APPEND_EQN] >>
  `bb.bb_label = LAST path` by metis_tac[lookup_block_label] >>
  metis_tac[EL_MEM]
QED

Theorem current_live_post_phi_single_definition:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  i <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) l i) /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\ fn_dominates fn db.bb_label l /\
    (db = bb ==> ?j. j < i /\ MEM v (EL j bb.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `current_available fn v l i` by metis_tac[current_live_post_phi_available] >>
  drule_all current_available_definition >> strip_tac >>
  qexistsl_tac [`db`, `di`] >> simp[] >> conj_tac
  >- metis_tac[current_available_unique_dominates] >>
  metis_tac[current_available_local_index]
QED

Theorem current_collect_phis_length:
  !insts. LENGTH (collect_phis insts) <= LENGTH insts
Proof
  Induct >> simp[livenessDefsTheory.collect_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem current_live_phi_cut_single_definition:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) l
    (LENGTH (collect_phis bb.bb_instructions))) /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\ fn_dominates fn db.bb_label l /\
    (db = bb ==> ?j. j < LENGTH (collect_phis bb.bb_instructions) /\
      MEM v (EL j bb.bb_instructions).inst_outputs)
Proof
  strip_tac >> irule current_live_post_phi_single_definition >>
  simp[current_collect_phis_length]
QED
