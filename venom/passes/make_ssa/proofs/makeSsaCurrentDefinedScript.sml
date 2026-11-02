Theory makeSsaCurrentDefined
Ancestors
  makeSsaCurrentDemand venomExecProofs venomWf venomInst list relation
  sccpCorrectnessProofs finite_map pred_set

Theorem current_filter_single[local]:
  !xs x y. LENGTH (FILTER P xs) <= 1 /\ MEM x xs /\ MEM y xs /\
    P x /\ P y ==> x = y
Proof
  rpt strip_tac >>
  `MEM x (FILTER P xs) /\ MEM y (FILTER P xs)` by simp[MEM_FILTER] >>
  Cases_on `FILTER P xs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem current_single_def_block[local]:
  !bbs a b i j.
    LENGTH (FILTER (\i. MEM v i.inst_outputs)
      (FLAT (MAP (\bb. bb.bb_instructions) bbs))) <= 1 /\
    MEM a bbs /\ MEM b bbs /\ MEM i a.bb_instructions /\
    MEM j b.bb_instructions /\ MEM v i.inst_outputs /\
    MEM v j.inst_outputs ==> a = b
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[FILTER_APPEND_DISTRIB] >> rpt strip_tac >> gvs[]
  >- (`MEM i (FILTER (\i. MEM v i.inst_outputs) a.bb_instructions)` by simp[MEM_FILTER] >>
      `MEM j (FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs)))` by
        (simp[MEM_FILTER, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs) a.bb_instructions` >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs))` >> gvs[]) 
  >- (`MEM j (FILTER (\i. MEM v i.inst_outputs) b.bb_instructions)` by simp[MEM_FILTER] >>
      `MEM i (FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs)))` by
        (simp[MEM_FILTER, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs) b.bb_instructions` >>
      Cases_on `FILTER (\i. MEM v i.inst_outputs)
        (FLAT (MAP (\bb. bb.bb_instructions) bbs))` >> gvs[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem current_path_first_target[local]:
  !path. is_fn_path fn path /\ path <> [] /\ LAST path = target ==>
    ?pre. is_fn_path fn (pre ++ [target]) /\
      HD (pre ++ [target]) = HD path /\ ~MEM target pre
Proof
  Induct >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `h = target`
  >- (qexists_tac `[]` >> simp[is_fn_path_def]) >>
  Cases_on `path` >> gvs[is_fn_path_def] >>
  qexists_tac `h::pre` >> simp[] >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem current_insts_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem current_single_def_occurrence:
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  MEM i a.bb_instructions /\ MEM j b.bb_instructions /\
  MEM v i.inst_outputs /\ MEM v j.inst_outputs ==> a = b /\ i = j
Proof
  simp[fn_insts_def, current_insts_flat] >> rpt strip_tac
  >- (irule current_single_def_block >> metis_tac[]) >>
  irule current_filter_single >>
  qexists_tac `\i. MEM v i.inst_outputs` >>
  qexists_tac `FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)` >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_single_def_dominates[local]:
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_on_all_paths fn bb point v /\
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  fn_dominates fn db.bb_label bb.bb_label
Proof
  rpt strip_tac >> simp[fn_dominates_def] >> rpt strip_tac >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >> disch_then (qspec_then `path` mp_tac) >>
  simp[] >> strip_tac
  >- (`db = def_bb` by metis_tac[current_single_def_occurrence] >>
      gvs[] >> irule EL_MEM >> decide_tac) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `db = bb` by metis_tac[current_single_def_occurrence] >>
  gvs[] >> Cases_on `path` using SNOC_CASES >> gvs[]
QED

Theorem current_unique_def_available:
  wf_function fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_on_all_paths fn bb point v /\
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1 ==>
  def_available_at fn bb point v
Proof
  rpt strip_tac >>
  `?entry. fn_entry_label fn = SOME entry /\
    RTC (fn_cfg_edge fn) entry bb.bb_label` by gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all current_path_first_target >> strip_tac >>
  qpat_assum `def_on_all_paths _ _ _ _` mp_tac >>
  pure_rewrite_tac[def_on_all_paths_def] >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  simp[] >> strip_tac
  >- (`fn_dominates fn def_bb.bb_label bb.bb_label` by
        (irule current_single_def_dominates >> metis_tac[]) >>
      `def_bb <> bb` by
        (strip_tac >> gvs[] >>
         `k < LENGTH pre` by decide_tac >>
         `EL k (pre ++ [bb.bb_label]) = EL k pre` by simp[EL_APPEND_EQN] >>
         `MEM bb.bb_label pre` by metis_tac[EL_MEM] >> gvs[]) >>
      simp[def_available_at_def] >>
      qexistsl_tac [`def_bb`, `def_inst`] >> simp[]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `fn_dominates fn bb.bb_label bb.bb_label` by
    (irule current_single_def_dominates >> metis_tac[]) >>
  simp[def_available_at_def] >>
  qexistsl_tac [`bb`, `EL i bb.bb_instructions`] >> simp[] >>
  Cases_on `point` >> gvs[] >> metis_tac[]
QED

Theorem current_phi_operand_available:
  wf_function fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_on_all_paths fn bb point v /\
  fn_phi_operands_single_def fn /\ current_phi_operand fn v ==>
  def_available_at fn bb point v
Proof
  metis_tac[current_unique_def_available, current_phi_operand_single_def]
QED

Definition current_completed_blocks_def:
  (current_completed_blocks fn ctx [] st out <=> out = st) /\
  (current_completed_blocks fn ctx (lbl::ls) st out <=>
    ?bb fuel mid. lookup_block lbl fn.fn_blocks = SOME bb /\
      st.vs_current_bb = lbl /\ st.vs_inst_idx = 0 /\
      exec_block fuel ctx bb st = OK mid /\
      (ls <> [] ==> ~mid.vs_halted) /\
      current_completed_blocks fn ctx ls mid out)
End

Theorem current_completed_blocks_nil[simp]:
  current_completed_blocks fn ctx [] st out <=> out = st
Proof
  simp[current_completed_blocks_def]
QED

Theorem current_completed_blocks_single:
  current_completed_blocks fn ctx [lbl] st out <=>
    ?bb fuel. lookup_block lbl fn.fn_blocks = SOME bb /\
      st.vs_current_bb = lbl /\ st.vs_inst_idx = 0 /\
      exec_block fuel ctx bb st = OK out
Proof
  simp[current_completed_blocks_def]
QED

Theorem current_completed_blocks_fdom:
  !path st out. wf_function fn /\ fn_inst_wf fn /\
    current_completed_blocks fn ctx path st out ==>
    FDOM st.vs_vars SUBSET FDOM out.vs_vars
Proof
  Induct >> simp[current_completed_blocks_def] >> rpt strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
    (gvs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all exec_block_fdom_mono >> strip_tac >>
  first_x_assum drule_all >> metis_tac[SUBSET_TRANS]
QED

Theorem current_completed_blocks_output:
  !path st out. wf_function fn /\ fn_inst_wf fn /\
    current_completed_blocks fn ctx path st out /\ MEM lbl path /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
    v IN FDOM out.vs_vars
Proof
  Induct >> simp[current_completed_blocks_def] >> rpt strip_tac
  >- (gvs[] >>
      `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
        (gvs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
      `~is_terminator inst.inst_opcode` by
        (metis_tac[terminator_no_outputs, EVERY_MEM, MEM]) >>
      `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst` by
        metis_tac[MEM_EL] >>
      `v IN FDOM mid.vs_vars` by
        (irule exec_block_outputs_in_fdom >>
         qexistsl_tac [`bb`, `ctx`, `fuel`, `idx`, `st`] >> simp[]) >>
      drule_all current_completed_blocks_fdom >>
      simp[SUBSET_DEF]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_completed_blocks_append:
  !prefix st out.
    current_completed_blocks fn ctx (prefix ++ suffix) st out <=>
    ?mid. current_completed_blocks fn ctx prefix st mid /\
      (prefix <> [] /\ suffix <> [] ==> ~mid.vs_halted) /\
      current_completed_blocks fn ctx suffix mid out
Proof
  Induct >> simp[current_completed_blocks_def] >> rpt gen_tac >>
  Cases_on `prefix` >> simp[current_completed_blocks_def] >>
  eq_tac >> rpt strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem current_all_paths_endpoint_binding:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  def_on_all_paths fn bb NONE v /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label ==> v IN FDOM out.vs_vars
Proof
  rpt strip_tac >>
  qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (`MEM def_bb.bb_label path` by
        (gvs[] >> irule EL_MEM >> decide_tac) >>
      `lookup_block def_bb.bb_label fn.fn_blocks = SOME def_bb` by
        (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
      irule current_completed_blocks_output >> metis_tac[]) >>
  `MEM bb.bb_label path` by
    (Cases_on `path` using SNOC_CASES >> gvs[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  irule current_completed_blocks_output >> metis_tac[]
QED

Theorem current_phi_edge_endpoint_binding:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fn_defs_reach_uses fn /\ MEM succ fn.fn_blocks /\
  MEM phi succ.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (bb.bb_label,v) (phi_pairs phi.inst_operands) /\
  fn_cfg_edge fn bb.bb_label succ.bb_label /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label ==> v IN FDOM out.vs_vars
Proof
  rpt strip_tac >> irule current_all_paths_endpoint_binding >>
  qexistsl_tac [`bb`, `ctx`, `fn`, `path`, `st`] >> simp[] >>
  gvs[fn_defs_reach_uses_def] >> metis_tac[]
QED
