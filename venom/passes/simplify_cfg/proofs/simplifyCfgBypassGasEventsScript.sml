Theory simplifyCfgBypassGasEvents
Ancestors
  simplifyCfgGasEventBoundary simplifyCfgBypassTerminal gasEvents
  simplifyCfgBypassRuns simplifyCfgBypassExec simplifyCfgBypassShape
  simplifyCfgBypassEntry simplifyCfgBypassRootedEntry
  simplifyCfgBypassClosure simplifyCfgStaticInterface simplifyCfgDefs
  simplifyCfgControl simplifyCfgControlExec simplifyCfgFixupStatic
  venomExecSemantics venomExecProofs venomWf venomInst venomState
  simplifyCfgFragments simplifyCfgEndpoints simplifyCfgMergeRuns
  simplifyCfgSimTools simplifyCfgAvailability cfgTransform o1PassLift
  contextCodegenRel list simplifyCfgMergeSegment venomInstProofs instIdxIndep passSimulationDefs

Theorem scfg_bypass_gas_events_block_distance[local]:
  !d bb s t a b k C owner.
    LENGTH bb.bb_instructions - s.vs_inst_idx = d /\
    bb_well_formed bb /\
    phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
    scfg_bypass_aligned a b s t ==>
    gas_events_block k C owner (scfg_bypass_block a b bb) t =
    gas_events_block k C owner bb s
Proof
  completeInduct_on `d` >> rpt strip_tac >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    gvs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once gas_events_block_def, scfg_bypass_instruction] >>
      simp[Once gas_events_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  `i.inst_opcode <> PHI` by
    (`EVERY (\j. j.inst_opcode <> PHI)
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
     fs[get_instruction_def, EVERY_EL] >>
     first_x_assum (qspec_then
       `s.vs_inst_idx - phi_prefix_length bb.bb_instructions` mp_tac) >>
     simp[LENGTH_DROP, EL_DROP]) >>
  Cases_on `is_terminator i.inst_opcode`
  >- (simp[Once gas_events_block_def, scfg_bypass_instruction] >>
      simp[Once gas_events_block_def] >>
      `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
        (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
      `is_terminator (scfg_bypass_image a.bb_label b.bb_label
          (HD (bb_succs b)) bb.bb_label i).inst_opcode /\
       (scfg_bypass_image a.bb_label b.bb_label
          (HD (bb_succs b)) bb.bb_label i).inst_opcode <> GAS /\
       (scfg_bypass_image a.bb_label b.bb_label
          (HD (bb_succs b)) bb.bb_label i).inst_opcode <> INVOKE` by
        (qmatch_goalsub_abbrev_tac `is_terminator j.inst_opcode` >>
         `j.inst_opcode = i.inst_opcode \/
          j.inst_opcode = JMP /\ i.inst_opcode = JNZ` by
           metis_tac[scfg_bypass_image_opcode] >>
         gvs[is_terminator_def]) >>
      simp[gas_events_step_def] >>
      Cases_on `step_inst k C i s` >>
      Cases_on `step_inst k C
        (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i) t` >>
      simp[scfg_bypass_image_opcode]) >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME i` by
    (irule scfg_bypass_instruction_ordinary >> simp[]) >>
  `gas_events_step k C owner i t = gas_events_step k C owner i s` by
    gvs[scfg_bypass_aligned_def, scfg_ctrl_gas_events_step] >>
  simp[Once gas_events_block_def] >>
  Cases_on `step_inst k C i s`
  >- (drule_all scfg_bypass_ordinary_advance >> strip_tac >>
      CONV_TAC (RHS_CONV (SIMP_CONV (srw_ss()) [Once gas_events_block_def])) >>
      simp[] >> first_x_assum irule >>
      simp[] >> gvs[get_instruction_def]) >>
  drule scfg_bypass_ordinary_result >>
  disch_then (qspecl_then [`k`, `i`, `C`] mp_tac) >>
  Cases_on `step_inst k C i t` >>
  simp[scfg_result_def, Once gas_events_block_def]
QED

Theorem scfg_bypass_gas_events_block:
  bb_well_formed bb /\
  phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
  scfg_bypass_aligned a b s t ==>
  gas_events_block k C owner (scfg_bypass_block a b bb) t =
  gas_events_block k C owner bb s
Proof
  metis_tac[scfg_bypass_gas_events_block_distance]
QED

Theorem scfg_bypass_singleton_gas_events:
  scfg_bypass_hyp fn a b fn' ==>
  gas_events_block k C owner b s = []
Proof
  strip_tac >> drule scfg_bypass_singleton_shape >> strip_tac >>
  `LENGTH b.bb_instructions = 1` by
    (qpat_assum `b.bb_instructions = _` (once_rewrite_tac o single) >> simp[]) >>
  simp[Once gas_events_block_def, get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH b.bb_instructions` >> simp[] >>
  `s.vs_inst_idx = 0` by gvs[] >>
  simp[] >>
  qpat_assum `b.bb_instructions = _` (once_rewrite_tac o single) >>
  simp[gas_events_step_def, is_terminator_def] >>
  Cases_on `step_inst k C (LAST b.bb_instructions) s` >> simp[]
QED

Theorem scfg_bypass_entered_gas_events:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  enters_block fn s x ==>
  ?y. lookup_block t.vs_current_bb fn'.fn_blocks =
        SOME (scfg_bypass_block a b bb) /\
      enters_block fn' t y /\ scfg_bypass_aligned a b x y /\
      gas_events_block k C owner (scfg_bypass_block a b bb) y =
      gas_events_block k C owner bb x
Proof
  strip_tac >> drule_all scfg_bypass_rooted_entry_forward >> strip_tac >>
  `bb_well_formed bb` by
    (metis_tac[scfg_bypass_old_static, scfg_static_wf,
       wf_function_def, lookup_block_member_label]) >>
  qexists_tac `y` >> simp[] >> conj_tac
  >- (drule scfg_bypass_lookup_eq >>
      disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
      gvs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  irule scfg_bypass_gas_events_block >> simp[]
QED

Theorem scfg_bypass_terminator_successor_explicit:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  scfg_bypass_aligned a b s t /\ step_inst k C i s = OK u /\ ~u.vs_halted ==>
  ?v. step_inst k C
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t = OK v /\
    scfg_bprefix C fn u
      (if u.vs_current_bb = b.bb_label then jump_to (HD (bb_succs b)) u else u) /\
    scfg_bypass_aligned a b
      (if u.vs_current_bb = b.bb_label then jump_to (HD (bb_succs b)) u else u) v
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  Cases_on `s.vs_current_bb = a.bb_label`
  >- suspend "source" >>
  `u.vs_current_bb <> b.bb_label` by
    metis_tac[scfg_bypass_nonsource_successor] >>
  simp[] >> drule_all scfg_bypass_nonsource_branch >> strip_tac >>
  qexists_tac `v` >> simp[scfg_bprefix_rules]
QED

Resume scfg_bypass_terminator_successor_explicit[source]:
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  drule_all scfg_active_terminator_last >> strip_tac >>
  `MEM a fn.fn_blocks` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[lookup_block_member_label]) >>
  `bb = a` by metis_tac[same_label_same_block] >> gvs[] >>
  `~s.vs_halted` by
    (drule_all scfg_terminator_jump >>
     simp[jump_to_def, venom_state_component_equality]) >>
  drule_all scfg_bypass_source_successor_rooted >>
  disch_then (qspec_then
    `OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb` mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `u = jump_to l s` by gvs[] >> gvs[] >>
  `(LAST a.bb_instructions).inst_opcode <> PHI` by
    (Cases_on `(LAST a.bb_instructions).inst_opcode` >> gvs[is_terminator_def]) >>
  fs[scfg_bypass_aligned_def] >>
  Cases_on `l = b.bb_label` >>
  gvs[scfg_bypass_image_def, update_phi_bypass_def, jump_to_def]
QED
Finalise scfg_bypass_terminator_successor_explicit

Theorem scfg_bypass_exec_OK_explicit:
  !s. !C fn a b fn' s0 bb t k u.
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  scfg_bypass_aligned a b s t /\ exec_block k C bb s = OK u /\ ~u.vs_halted ==>
  ?v. exec_block k C (scfg_bypass_block a b bb) t = OK v /\
    scfg_bprefix C fn u
      (if u.vs_current_bb = b.bb_label then jump_to (HD (bb_succs b)) u else u) /\
    scfg_bypass_aligned a b
      (if u.vs_current_bb = b.bb_label then jump_to (HD (bb_succs b)) u else u) v
Proof
  rpt gen_tac >> qid_spec_tac `t` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `step_inst k C i s` >> simp[] >>
  rename1 `step_inst k C i s = OK next` >>
  Cases_on `is_terminator i.inst_opcode`
  >- suspend "transfer" >>
  simp[] >> strip_tac >> suspend "ordinary"
QED

Resume scfg_bypass_exec_OK_explicit[transfer]:
  qpat_x_assum `!y. LENGTH _ - _ < _ ==> _` kall_tac >>
  Cases_on `next.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
  `frame_reach C fn s0 i s` by metis_tac[] >>
  drule_all scfg_bypass_terminator_successor_explicit >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME
     (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i)` by
    (simp[scfg_bypass_instruction] >> metis_tac[]) >>
  `is_terminator (scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) bb.bb_label i).inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  `~v.vs_halted` by
    (qpat_x_assum `scfg_bypass_aligned a b _ v` mp_tac >>
     Cases_on `next.vs_current_bb = b.bb_label` >>
     simp[scfg_bypass_aligned_def, scfg_ctrl_def, jump_to_def] >>
     strip_tac >> simp[]) >>
  simp[Once exec_block_def]
QED

Resume scfg_bypass_exec_OK_explicit[ordinary]:
  `i.inst_opcode <> PHI` by metis_tac[scfg_step_OK_nonphi] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  `next.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `!j. get_instruction bb (SUC s.vs_inst_idx) = SOME j ==>
    frame_reach C fn s0 j (next with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >> irule (cj 2 frame_reach_rules) >> conj_tac
     >- (simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
     qexistsl_tac [`k`, `i`] >> simp[]) >>
  drule_all scfg_bypass_ordinary_advance >> strip_tac >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qspec_then `next with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspec_then
    `(scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s.vs_inst_idx next) with vs_inst_idx := SUC t.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v2` strip_assume_tac) >>
  qexists_tac `v2` >> simp[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME i` by
    (irule scfg_bypass_instruction_ordinary >> metis_tac[]) >>
  simp[Once exec_block_def] >> metis_tac[]
QED
Finalise scfg_bypass_exec_OK_explicit

Theorem scfg_bypass_run_block_OK_explicit:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k C bb s = OK u /\ ~u.vs_halted ==>
  ?v. run_block k C (scfg_bypass_block a b bb) t = OK v /\
    scfg_bprefix C fn u
      (if u.vs_current_bb = b.bb_label then jump_to (HD (bb_succs b)) u else u) /\
    scfg_bypass_aligned a b
      (if u.vs_current_bb = b.bb_label then jump_to (HD (bb_succs b)) u else u) v
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, scfg_static_inst_wf] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `(case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb)` by
    (drule_all scfg_bprefix_incoming >> strip_tac >> gvs[fn_entry_state_def]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[run_block_def] >> strip_tac >>
  rename1 `eval_phis s bb.bb_instructions = OK r` >>
  `enters_block fn s (r with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    simp[enters_block_def] >>
  `!i. get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME i ==>
    frame_reach C fn s0 i (r with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (rpt strip_tac >> irule scfg_bprefix_enter_reach >>
     reverse conj_tac >- (qexists_tac `s` >> simp[]) >>
     irule scfg_lookup_active >> qexistsl_tac [`s`, `bb`] >> simp[] >>
     metis_tac[eval_phis_preserves_current_bb]) >>
  drule_all scfg_bypass_eval_phis >>
  disch_then (qspecl_then [`s.vs_inst_idx`, `s.vs_current_bb`] assume_tac) >>
  `r.vs_current_bb = s.vs_current_bb /\ r.vs_prev_bb = s.vs_prev_bb` by
    (drule eval_phis_only_updates_vs_vars >> disch_then SUBST1_TAC >> simp[]) >>
  `scfg_bypass_aligned a b (r with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    ((scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 r)
      with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `bb.bb_label = (r with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb` by simp[] >>
  `eval_phis t (scfg_bypass_block a b bb).bb_instructions =
    OK (scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 r)` by
    (qpat_x_assum `eval_phis (scfg_ctrl _ _ _ _) _ = _` mp_tac >>
     fs[exec_result_map_def, scfg_bypass_aligned_def]) >>
  simp[run_block_def, scfg_bypass_phi_prefix_length] >>
  irule scfg_bypass_exec_OK_explicit >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`r with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `s0`] >> simp[]) >>
  metis_tac[]
QED

Theorem scfg_bypass_exec_terminal_fixed:
  !d bb s t C fn a b fn' s0 k r.
  LENGTH bb.bb_instructions - s.vs_inst_idx = d /\
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
  scfg_bypass_aligned a b s t /\ exec_block k C bb s = r /\
  terminates r /\ (!v. r <> OK v) ==>
  scfg_result r (exec_block k C (scfg_bypass_block a b bb) t)
Proof
  completeInduct_on `d` >> rpt strip_tac >>
  `t.vs_inst_idx = s.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `bb_well_formed bb` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, wf_function_bb_well_formed] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (strip_tac >> gvs[terminates_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  `i.inst_opcode <> PHI` by
    (`EVERY (\j. j.inst_opcode <> PHI)
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
     fs[get_instruction_def, EVERY_EL] >>
     first_x_assum (qspec_then
       `s.vs_inst_idx - phi_prefix_length bb.bb_instructions` mp_tac) >>
     simp[LENGTH_DROP, EL_DROP]) >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME
     (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i)` by
    simp[scfg_bypass_instruction] >>
  `frame_reach C fn s0 i s` by metis_tac[] >>
  drule_all scfg_bypass_step_result >>
  disch_then (qspec_then `k` assume_tac) >>
  Cases_on `is_terminator i.inst_opcode`
  >- suspend "terminal" >>
  suspend "ordinary"
QED

Resume scfg_bypass_exec_terminal_fixed[terminal]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `is_terminator (scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) bb.bb_label i).inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  disch_then (SUBST_ALL_TAC o SYM) >> gvs[] >>
  Cases_on `step_inst k C i s` >>
  Cases_on `step_inst k C
     (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t` >>
  fs[scfg_result_def] >>
  simp[Once exec_block_def] >>
  fs[scfg_result_def] >>
  rename1 `scfg_payload p q` >>
  `q.vs_halted = p.vs_halted` by
    (qpat_x_assum `scfg_payload p q` mp_tac >>
     simp[scfg_payload_def, scfg_ctrl_def] >> strip_tac >>
     qpat_x_assum `q = _` SUBST1_TAC >> simp[]) >>
  Cases_on `p.vs_halted` >> simp[scfg_result_def]
QED

Resume scfg_bypass_exec_terminal_fixed[ordinary]:
  simp[] >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME i` by
    (irule scfg_bypass_instruction_ordinary >> simp[]) >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  Cases_on `step_inst k C i s`
  >- suspend "advance" >>
  drule_all scfg_bypass_ordinary_result >>
  disch_then (qspecl_then [`k`, `i`, `C`] assume_tac) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  Cases_on `step_inst k C i t` >>
  gvs[scfg_result_def] >>
  simp[Once exec_block_def, scfg_result_def]
QED

Resume scfg_bypass_exec_terminal_fixed[advance]:
  rename1 `step_inst k C i s = OK next` >>
  gvs[] >>
  drule_all scfg_bypass_ordinary_advance >> strip_tac >>
  CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once exec_block_def])) >>
  simp[] >> first_x_assum irule >>
  `next.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  simp[] >> conj_tac >- gvs[] >>
  qexistsl_tac [`fn`, `fn'`, `s0`] >> simp[] >>
  rpt strip_tac >> irule (cj 2 frame_reach_rules) >> conj_tac
  >- (simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
  qexistsl_tac [`k`, `i`] >> simp[]
QED
Finalise scfg_bypass_exec_terminal_fixed

Theorem scfg_bypass_run_block_terminal_fixed:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k C bb s = r /\ terminates r /\ (!v. r <> OK v) ==>
  scfg_result r (run_block k C (scfg_bypass_block a b bb) t)
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> fs[terminates_def]) >>
  drule_all scfg_run_block_entry >> strip_tac >>
  drule_all scfg_bypass_rooted_entry_forward >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `phi_prefix_length bb.bb_instructions <= x.vs_inst_idx` by simp[] >>
  `scfg_result r (exec_block k C (scfg_bypass_block a b bb) y)` by
    (irule scfg_bypass_exec_terminal_fixed >> simp[] >>
     qexistsl_tac [`fn`, `fn'`, `x`, `s0`] >> simp[]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >> disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  drule_all scfg_enters_block_run_block >>
  disch_then (qspecl_then [`k`, `C`] assume_tac) >> metis_tac[]
QED

Theorem scfg_bypass_skip_block_boundary:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 u /\ u.vs_current_bb = b.bb_label /\
  u.vs_inst_idx = 0 /\ ~u.vs_halted ==>
  enters_block fn u u /\
  (!j. run_block j C b u = OK (jump_to (HD (bb_succs b)) u)) /\
  (!j owner. gas_events_block j C owner b u = []) /\
  (jump_to (HD (bb_succs b)) u).vs_inst_idx = 0
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    (drule scfg_bypass_singleton_shape >> strip_tac >>
     qpat_assum `b.bb_instructions = [_]` (once_rewrite_tac o single) >> simp[]) >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME b` by fs[scfg_bypass_hyp_def] >>
  `enters_block fn u u` by
    (simp[enters_block_def] >> qexists_tac `u` >>
     simp[eval_phis_no_phis, no_phis_phi_prefix_length_zero] >>
     simp[venom_state_component_equality]) >>
  `MEM b fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `active_inst fn (LAST b.bb_instructions) u` by
    (simp[active_inst_def] >> qexists_tac `b` >> simp[get_instruction_def] >>
     drule scfg_bypass_singleton_shape >> strip_tac >>
     qpat_assum `b.bb_instructions = [_]` (once_rewrite_tac o single) >> simp[]) >>
  `frame_reach C fn s0 (LAST b.bb_instructions) u` by
    metis_tac[scfg_bprefix_enter_reach] >>
  simp[jump_to_def] >> conj_tac
  >- (gen_tac >> drule_all scfg_bypass_singleton_run >> simp[jump_to_def]) >>
  rpt gen_tac >> irule scfg_bypass_singleton_gas_events >>
  goal_assum drule
QED

Theorem scfg_bypass_gas_runs_forward:
  !n s t. scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
    scfg_bprefix C fn s0 s /\ scfg_bypass_aligned a b s t /\
    s.vs_inst_idx = 0 ==>
    ?m extra. gas_events_blocks m C fn' t = gas_events_blocks n C fn s ++ extra /\
      (terminates (run_blocks n C fn s) ==> extra = [] /\
        scfg_result (run_blocks n C fn s) (run_blocks m C fn' t))
Proof
  completeInduct_on `n` >> Cases_on `n`
  >- (rpt strip_tac >> qexistsl_tac [`0`, `[]`] >>
      simp[Ntimes gas_events_blocks_def 2, Once run_blocks_def, terminates_def]) >>
  rename1 `SUC k` >> rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qexistsl_tac [`0`, `[]`] >>
      simp[Ntimes gas_events_blocks_def 2, Once run_blocks_def, terminates_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `?sp. eval_phis s bb.bb_instructions = OK sp`
  >- (pop_assum strip_assume_tac >> suspend "entry") >>
  `?e. eval_phis s bb.bb_instructions = Error e` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  qexistsl_tac [`0`, `[]`] >>
  simp[Ntimes gas_events_blocks_def 2, Once run_blocks_def, run_block_def, terminates_def]
QED

Resume scfg_bypass_gas_runs_forward[entry]:
  qabbrev_tac `s1 = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `enters_block fn s s1` by
    (simp[enters_block_def, Abbr `s1`] >> metis_tac[]) >>
  `?t1. lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb) /\
    enters_block fn' t t1 /\ scfg_bypass_aligned a b s1 t1 /\
    gas_events_block k C fn.fn_name (scfg_bypass_block a b bb) t1 =
      gas_events_block k C fn.fn_name bb s1` by
    (irule scfg_bypass_entered_gas_events >> simp[] >> metis_tac[]) >>
  `fn'.fn_name = fn.fn_name` by metis_tac[scfg_bypass_name] >>
  Cases_on `?u. run_block k C bb s = OK u`
  >- (pop_assum strip_assume_tac >> suspend "ok") >>
  suspend "nonok"
QED

Resume scfg_bypass_gas_runs_forward[ok]:
  `~u.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `scfg_bprefix C fn s0 u` by
    metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
  drule_all scfg_bypass_run_block_OK_explicit >> strip_tac >>
  `u.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  Cases_on `u.vs_current_bb = b.bb_label`
  >- suspend "skip" >>
  gvs[] >>
  `?j tail. gas_events_blocks j C fn' v = gas_events_blocks k C fn u ++ tail /\
    (terminates (run_blocks k C fn u) ==> tail = [] /\
      scfg_result (run_blocks k C fn u) (run_blocks j C fn' v))` by
    (qpat_x_assum `!m. m < SUC k ==> _` irule >> simp[] >> metis_tac[]) >>
  suspend "sync"
QED

Resume scfg_bypass_gas_runs_forward[skip]:
  gvs[] >>
  drule_all scfg_bypass_skip_block_boundary >> strip_tac >>
  Cases_on `k` >- suspend "skip_zero" >>
  rename1 `run_block (SUC h) C bb s = OK u` >>
  `scfg_bprefix C fn s0 (jump_to (HD (bb_succs b)) u)` by
    metis_tac[scfg_bprefix_trans] >>
  `?j tail. gas_events_blocks j C fn' v =
    gas_events_blocks h C fn (jump_to (HD (bb_succs b)) u) ++ tail /\
    (terminates (run_blocks h C fn (jump_to (HD (bb_succs b)) u)) ==>
      tail = [] /\ scfg_result (run_blocks h C fn (jump_to (HD (bb_succs b)) u))
        (run_blocks j C fn' v))` by
    (qpat_x_assum `!m. m < SUC (SUC h) ==> _` irule >> simp[] >> metis_tac[]) >>
  `gas_events_blocks (SUC h) C fn u =
    gas_events_blocks h C fn (jump_to (HD (bb_succs b)) u)` by
    (`lookup_block u.vs_current_bb fn.fn_blocks = SOME b` by fs[scfg_bypass_hyp_def] >>
     qpat_assum `enters_block fn u u` mp_tac >>
     pure_rewrite_tac[enters_block_def] >> strip_tac >>
     `exec_block h C b u = OK (jump_to (HD (bb_succs b)) u)` by
       metis_tac[simplifyCfgMergeGlobalRunsTheory.scfg_enter_run_block] >>
     CONV_TAC (LAND_CONV (REWR_CONV gas_events_blocks_def)) >>
     `bb' = b` by
       (qpat_assum `lookup_block u.vs_current_bb _ = SOME b` mp_tac >> simp[]) >>
     qpat_x_assum `bb' = b` SUBST_ALL_TAC >>
     qpat_assum `lookup_block u.vs_current_bb _ = SOME b` (pure_rewrite_tac o single) >>
     simp_tac (srw_ss()) [] >>
     qpat_assum `eval_phis u _ = OK _` (pure_rewrite_tac o single) >>
     simp_tac (srw_ss()) [] >>
     qpat_x_assum `u = _ with vs_inst_idx := _` (pure_rewrite_tac o single o SYM) >>
     simp[jump_to_def]) >>
  `run_blocks (SUC h) C fn u = run_blocks h C fn (jump_to (HD (bb_succs b)) u)` by
    (simp[run_blocks_unfold] >> fs[scfg_bypass_hyp_def] >> simp[jump_to_def]) >>
  qpat_x_assum `gas_events_blocks (SUC h) C fn u = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  qpat_x_assum `run_blocks (SUC h) C fn u = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  suspend "skip_sync"
QED

fun scfg_bypass_sync_tac g = (
  rename1 `run_block k C bb s = OK u` >>
  qpat_x_assum `!m. m < SUC k ==> _` kall_tac >>
  `?tp. eval_phis t (scfg_bypass_block a b bb).bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length (scfg_bypass_block a b bb).bb_instructions` by
    (fs[enters_block_def] >> gvs[]) >>
  `exec_block k C (scfg_bypass_block a b bb) t1 = OK v` by
    metis_tac[simplifyCfgMergeGlobalRunsTheory.scfg_enter_run_block] >>
  `exec_block k C bb s1 = OK u` by metis_tac[simplifyCfgMergeGlobalRunsTheory.scfg_enter_run_block] >>
  `~v.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `k <= MAX k j` by simp[] >>
  drule (cj 2 gasEventsFuelTheory.gas_events_fuel_extension) >>
  disch_then (qspecl_then [`C`, `fn.fn_name`, `scfg_bypass_block a b bb`, `t1`] mp_tac) >>
  simp[] >> strip_tac >>
  `j <= MAX k j` by simp[] >>
  drule (cj 3 gasEventsFuelTheory.gas_events_fuel_extension) >>
  disch_then (qspecl_then [`C`, `fn'`, `v`] strip_assume_tac) >>
  rename1 `gas_events_blocks (MAX k j) C fn' v = gas_events_blocks j C fn' v ++ more` >>
  gvs[Abbr `s1`] >>
  qexistsl_tac [`SUC (MAX k j)`, `tail ++ more`] >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
  simp[APPEND_ASSOC] >> strip_tac >>
  `scfg_result (run_blocks k C fn u) (run_blocks j C fn' v)` by metis_tac[] >>
  `terminates (run_blocks j C fn' v)` by
    (Cases_on `run_blocks k C fn u` >> Cases_on `run_blocks j C fn' v` >>
     gvs[terminates_def, scfg_result_def]) >>
  `!err. run_blocks j C fn' v <> Error err` by
    (Cases_on `run_blocks j C fn' v` >> gvs[terminates_def]) >>
  gvs[]) g;

Resume scfg_bypass_gas_runs_forward[sync]:
  scfg_bypass_sync_tac
QED

Resume scfg_bypass_gas_runs_forward[skip_sync]:
  scfg_bypass_sync_tac
QED

Resume scfg_bypass_gas_runs_forward[skip_zero]:
  `?tp. eval_phis t (scfg_bypass_block a b bb).bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length (scfg_bypass_block a b bb).bb_instructions` by
    (fs[enters_block_def] >> gvs[]) >>
  `exec_block 0 C bb s1 = OK u` by
    metis_tac[simplifyCfgMergeGlobalRunsTheory.scfg_enter_run_block] >>
  `exec_block 0 C (scfg_bypass_block a b bb) t1 = OK v` by
    metis_tac[simplifyCfgMergeGlobalRunsTheory.scfg_enter_run_block] >>
  gvs[Abbr `s1`] >>
  qexistsl_tac [`SUC 0`, `[]`] >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
  simp[Ntimes gas_events_blocks_def 2, Ntimes run_blocks_def 2, terminates_def]
QED

Resume scfg_bypass_gas_runs_forward[nonok]:
  qpat_x_assum `!m. m < SUC k ==> _` kall_tac >>
  `run_blocks (SUC k) C fn s = run_block k C bb s` by
    (Cases_on `run_block k C bb s` >> gvs[run_blocks_unfold]) >>
  `?tp. eval_phis t (scfg_bypass_block a b bb).bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length (scfg_bypass_block a b bb).bb_instructions` by
    (fs[enters_block_def] >> gvs[]) >>
  `run_block k C bb s = exec_block k C bb s1` by simp[run_block_def, Abbr `s1`] >>
  `terminates (run_block k C bb s) ==>
    scfg_result (run_block k C bb s) (run_block k C (scfg_bypass_block a b bb) t)` by
    (strip_tac >> irule scfg_bypass_run_block_terminal_fixed >> simp[] >> metis_tac[]) >>
  `run_block k C (scfg_bypass_block a b bb) t =
    exec_block k C (scfg_bypass_block a b bb) t1` by simp[run_block_def] >>
  qexists_tac `SUC k` >>
  Cases_on `run_block k C bb s` >>
  Cases_on `run_block k C (scfg_bypass_block a b bb) t` >>
  gvs[terminates_def, scfg_result_def] >>
  pure_once_rewrite_tac[gas_events_blocks_def] >>
  gvs[run_block_def, run_blocks_unfold, Abbr `s1`] >>
  rpt (qpat_x_assum `_ = exec_block _ _ _ _` (SUBST_ALL_TAC o SYM)) >>
  simp[terminates_def, scfg_result_def]
QED
Finalise scfg_bypass_gas_runs_forward

Theorem scfg_bypass_gas_entry_forward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s ==>
  !n. ?m extra.
    gas_events_blocks m C fn' s = gas_events_blocks n C fn s ++ extra /\
    (terminates (run_blocks n C fn s) ==> extra = [] /\
      frame_result_rel (run_blocks n C fn s) (run_blocks m C fn' s))
Proof
  rpt strip_tac >>
  `scfg_bprefix C fn s s` by simp[scfg_bprefix_rules] >>
  `scfg_bypass_aligned a b s s` by
    metis_tac[simplifyCfgBypassSemanticsTheory.scfg_bypass_initial_aligned] >>
  `s.vs_inst_idx = 0` by fs[fn_entry_state_def] >>
  drule_all scfg_bypass_gas_runs_forward >>
  disch_then (qspec_then `n` strip_assume_tac) >>
  qexistsl_tac [`m`, `extra`] >> simp[] >> strip_tac >>
  irule scfg_result_terminal >> simp[run_blocks_not_OK] >> metis_tac[]
QED
