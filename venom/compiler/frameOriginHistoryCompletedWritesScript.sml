Theory frameOriginHistoryCompletedWrites
Ancestors
  frameOriginHistoryPreservation frameOriginHistoryEntries
  frameOriginHistoryOccurrences frameOriginHistory venomExecProofs
  frameHistoryDefinitions frameHistoryCfg frameHistoryInstructions
  frameHistoryCompleted frameExecutionHistory frameCfgBoundary venomWf venomInstProps
  contextCodegenRel venomExecSemantics venomState venomInst finite_map pred_set list rich_list

Theorem eval_phis_reset_writes:
  eval_phis pre is = OK post /\ pre.vs_prev_bb = NONE ==>
  origin_phi_writes is = {} /\ phi_prefix_length is = 0
Proof
  Cases_on `is` >> simp[eval_phis_def, origin_phi_writes_def, phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, origin_phi_writes_def, phi_prefix_length_def,
       eval_one_phi_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem enters_block_reset_writes:
  enters_block fn pre s /\ pre.vs_prev_bb = NONE ==>
  origin_entry_writes fn pre = {}
Proof
  simp[enters_block_def, origin_entry_writes_def] >> rpt strip_tac >>
  simp[] >> metis_tac[eval_phis_reset_writes]
QED

Theorem setup_callee_no_predecessor:
  setup_callee fn args caller = SOME callee ==> callee.vs_prev_bb = NONE
Proof
  simp[setup_callee_def] >> rpt strip_tac >> gvs[]
QED

Definition origin_completed_writes_def:
  origin_completed_writes [] = {} /\
  origin_completed_writes [a] = {} /\
  origin_completed_writes [a;b] = {} /\
  origin_completed_writes (a::e::b::rest) =
    (case (a,b) of
       (OriginObserve src,OriginObserve dst) => origin_edge_writes src e
     | _ => {}) UNION origin_completed_writes (e::b::rest)
End

Theorem origin_completed_writes_start[simp]:
  origin_completed_writes [start;OriginObserve a] = {}
Proof
  simp[origin_completed_writes_def]
QED

Theorem origin_completed_writes_append:
  !h. h <> [] /\ LAST h = OriginObserve a /\
    (!snap. e <> OriginObserve snap) ==>
    origin_completed_writes (h ++ [e;OriginObserve b]) =
    origin_completed_writes h UNION origin_edge_writes a e
Proof
  recInduct origin_completed_writes_ind >>
  simp[origin_completed_writes_def] >> rpt strip_tac >>
  gvs[UNION_ASSOC] >> Cases_on `a'` >> Cases_on `e` >> gvs[]
QED

Theorem origin_completed_writes_cons:
  origin_completed_writes h SUBSET origin_completed_writes (ev::h)
Proof
  Cases_on `h` >> simp[origin_completed_writes_def] >>
  Cases_on `t` >> simp[origin_completed_writes_def, SUBSET_UNION]
QED

Theorem origin_completed_writes_prefix:
  !pre h. origin_completed_writes h SUBSET origin_completed_writes (pre ++ h)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  metis_tac[SUBSET_TRANS, origin_completed_writes_cons]
QED

Theorem origin_completed_writes_occurrence:
  h = pre ++ OriginObserve a::e::OriginObserve b::rest /\
  v IN origin_edge_writes a e ==> v IN origin_completed_writes h
Proof
  strip_tac >> gvs[] >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  `v IN origin_completed_writes (OriginObserve a::e::OriginObserve b::rest)` by
    simp[origin_completed_writes_def] >>
  qspecl_then [`pre`, `OriginObserve a::e::OriginObserve b::rest`] mp_tac
    origin_completed_writes_prefix >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem origin_completed_observation_write:
  origin_log ctx h /\ MEM (di,ds) (FRONT (origin_observations h)) /\
  inst_wf di /\ MEM v di.inst_outputs ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule_all origin_observations_completion >> strip_tac >>
  `v IN origin_edge_writes (OriginSnapshot fn PG G om di ds) e` by
    (Cases_on `b` >> Cases_on `e` >> gvs[origin_edge_def, origin_edge_writes_def] >>
     metis_tac[terminator_no_outputs, MEM]) >>
  irule origin_completed_writes_occurrence >> metis_tac[]
QED

Definition origin_reset_predecessor_def:
  origin_reset_predecessor e =
    case e of OriginInitial pre => pre.vs_prev_bb = NONE
    | OriginCallee pre => pre.vs_prev_bb = NONE | _ => T
End

Theorem joint_origin_history_reset_predecessors:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
  EVERY origin_reset_predecessor h /\
  EVERY (EVERY origin_reset_predecessor) hs
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt strip_tac >>
  gvs[origin_reset_predecessor_def] >>
  metis_tac[setup_callee_no_predecessor]
QED

Theorem origin_phi_writes_index:
  !is k. k < phi_prefix_length is /\ k < LENGTH is /\
    MEM v (EL k is).inst_outputs ==> v IN origin_phi_writes is
Proof
  Induct >> simp[phi_prefix_length_def, origin_phi_writes_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `k` >> simp[] >> metis_tac[]
QED

Theorem origin_visited_phi_write:
  origin_entry_witness ctx fn lbl h /\ EVERY origin_reset_predecessor h /\
  wf_function fn /\ MEM db fn.fn_blocks /\ db.bb_label = lbl /\
  k < phi_prefix_length db.bb_instructions /\ k < LENGTH db.bb_instructions /\
  MEM v (EL k db.bb_instructions).inst_outputs ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule origin_phi_writes_index >> strip_tac >>
  drule origin_entry_witness_cases >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (gvs[origin_reset_predecessor_def] >>
      drule_all enters_block_reset_writes >> strip_tac >>
      gvs[enters_block_def, origin_entry_writes_def] >>
      drule eval_phis_preserves_current_bb >> strip_tac >>
      `db = bb` by metis_tac[same_label_same_block, lookup_block_MEM, lookup_block_label] >> gvs[]) >>
  gvs[] >>
  `v IN origin_entry_writes fn post` by
    (gvs[enters_block_def, origin_entry_writes_def] >>
     drule eval_phis_preserves_current_bb >> strip_tac >>
     `db = bb` by metis_tac[same_label_same_block, lookup_block_MEM, lookup_block_label] >>
     gvs[]) >>
  irule origin_completed_writes_occurrence >>
  qexistsl [`OriginSnapshot fn PG G om inst s`,
    `OriginSnapshot fn PG (entry_prov fn post G) (origin_entry fn post om) inst' t`,
    `OriginBlock fuel post`, `prefix`, `tail`] >>
  simp[origin_edge_writes_def]
QED

Theorem joint_origin_history_definition_completed_write:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  ((?di ds. MEM (di,ds) (FRONT (origin_observations h)) /\
       active_inst fn di ds /\ MEM v di.inst_outputs) \/
   (?db k. MEM db fn.fn_blocks /\
       MEM db.bb_label (history_visits (origin_observations h)) /\
       k < phi_prefix_length db.bb_instructions /\ k < LENGTH db.bb_instructions /\
       MEM v (EL k db.bb_instructions).inst_outputs)) ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule joint_origin_history_projection >> strip_tac
  >- (irule origin_completed_observation_write >> reverse conj_tac
      >- metis_tac[joint_origin_history_current_log] >>
      qexistsl [`di`, `ds`] >> simp[] >>
      `MEM fn ctx.ctx_functions` by metis_tac[frame_history_cfg_invariant] >>
      gvs[active_inst_def, EVERY_MEM, fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  irule origin_visited_phi_write >> conj_tac
  >- metis_tac[joint_origin_history_reset_predecessors] >>
  qexistsl [`ctx`, `db`, `fn`, `k`, `db.bb_label`] >> simp[] >>
  metis_tac[joint_origin_history_visited_entry, frame_history_cfg_invariant, EVERY_MEM]
QED

Theorem joint_origin_history_ordinary_completed_write:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> irule joint_origin_history_definition_completed_write >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[joint_origin_history_projection, frame_history_ordinary_use_definition]
QED

Theorem def_on_all_paths_before_terminator:
  bb_well_formed bb /\ MEM inst bb.bb_instructions /\
  inst_wf inst /\ is_terminator inst.inst_opcode /\
  def_on_all_paths fn bb NONE v ==>
  def_on_all_paths fn bb (SOME inst) v
Proof
  strip_tac >>
  `inst.inst_outputs = []` by metis_tac[terminator_no_outputs] >>
  gvs[def_on_all_paths_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexists `i` >> simp[] >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `j = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  qexists `j` >> simp[] >>
  `i <> j` by (strip_tac >> gvs[]) >> decide_tac
QED

Theorem joint_origin_history_available_completed_write:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  ctx_inst_ids_distinct ctx /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ def_on_all_paths fn bb (SOME inst) v ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule joint_origin_history_projection >> strip_tac >>
  drule joint_origin_history_definition_completed_write >> simp[] >>
  disch_then irule >>
  drule_all frame_history_cfg_invariant >> strip_tac >>
  drule_all frame_history_current_instruction_prefix >> strip_tac >>
  drule_all frame_history_current_completed >> strip_tac >>
  drule frame_history_active >> strip_tac >>
  irule history_available_definition >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[EVERY_MEM] >>
  qexists `bb` >> simp[] >>
  metis_tac[active_instruction_unique_index, EVERY_MEM]
QED

Theorem joint_origin_history_phi_edge_completed_write:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
  ~post.vs_halted /\ enters_block fn post t /\
  MEM target fn.fn_blocks /\ target.bb_label = t.vs_current_bb /\
  MEM phi target.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (s.vs_current_bb,v) (phi_pairs phi.inst_operands) ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule joint_origin_history_projection >> strip_tac >>
  drule_all frame_history_cfg_invariant >> strip_tac >>
  drule frame_history_active >> strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn` by
    metis_tac[EVERY_MEM] >>
  drule_all active_terminator_cfg_transition >> strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
        MEM inst bb.bb_instructions` by
    (gvs[active_inst_def] >> metis_tac[EL_MEM]) >>
  `def_on_all_paths fn bb NONE v` by
    (gvs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  `def_on_all_paths fn bb (SOME inst) v` by
    (irule def_on_all_paths_before_terminator >> simp[] >>
     metis_tac[wf_function_def, fn_inst_wf_def]) >>
  drule joint_origin_history_available_completed_write >> simp[] >>
  disch_then irule >> metis_tac[]
QED

Theorem resolve_phi_var_pair:
  !ops lbl v. resolve_phi lbl ops = SOME (Var v) ==>
    MEM (lbl,v) (phi_pairs ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[resolve_phi_def, phi_pairs_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `v1` >> gvs[resolve_phi_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem joint_origin_history_selected_phi_completed_write:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
  ~post.vs_halted /\ enters_block fn post t /\
  MEM target fn.fn_blocks /\ target.bb_label = t.vs_current_bb /\
  MEM phi target.bb_instructions /\ phi.inst_opcode = PHI /\
  resolve_phi s.vs_current_bb phi.inst_operands = SOME (Var v) ==>
  v IN origin_completed_writes h
Proof
  strip_tac >> drule resolve_phi_var_pair >> strip_tac >>
  drule joint_origin_history_phi_edge_completed_write >> simp[] >>
  disch_then irule >> metis_tac[]
QED
