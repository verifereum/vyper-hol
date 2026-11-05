(* Terminal results are insensitive to the contracted control coordinates. *)
Theory simplifyCfgBypassTerminal
Ancestors
  simplifyCfgBypassRuns simplifyCfgBypassExec simplifyCfgBypassEntry simplifyCfgBypassShape
  simplifyCfgControl simplifyCfgControlExec simplifyCfgMergeRuns
  simplifyCfgStaticInterface simplifyCfgFragments simplifyCfgDefs simplifyCfgSimTools
  simplifyCfgBypassPrecondition simplifyCfgBypassClosure cfgTransform venomExecSemantics venomExecProofs
  venomExecProps venomInst venomState venomWf o1PassLift list
  simplifyCfgEndpoints simplifyCfgBypassRootedEntry simplifyCfgFixupStatic
  passSimulationDefs

Theorem scfg_bypass_step_result:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ i.inst_opcode <> PHI /\
  scfg_bypass_aligned a b s t ==>
  scfg_result (step_inst k C i s)
    (step_inst k C
      (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t)
Proof
  strip_tac >>
  Cases_on `s.vs_current_bb = a.bb_label /\ is_terminator i.inst_opcode`
  >- suspend "source" >>
  `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i = i` by
    (Cases_on `is_terminator i.inst_opcode`
     >- (gvs[scfg_bypass_image_def, update_phi_bypass_def]) >>
     simp[scfg_bypass_image_ordinary]) >>
  fs[scfg_bypass_aligned_def] >> irule scfg_ctrl_step_result
QED

Resume scfg_bypass_step_result[source]:
  fs[] >>
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  drule_all scfg_active_terminator_last >> strip_tac >>
  `MEM a fn.fn_blocks` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[lookup_block_member_label]) >>
  `bb = a` by metis_tac[same_label_same_block] >> gvs[] >>
  drule_all scfg_bypass_source_step >>
  disch_then (qspec_then
    `OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb` mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `a.bb_label` mp_tac) >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  fs[scfg_bypass_aligned_def] >>
  simp[scfg_bypass_image_def, update_phi_bypass_def, scfg_result_def] >>
  simp[scfg_payload_def, jump_to_def, scfg_ctrl_def]
QED
Finalise scfg_bypass_step_result

Theorem scfg_bypass_exec_terminal_forward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
  scfg_bypass_aligned a b s t /\ exec_block k C bb s = r /\
  terminates r /\ (!v. r <> OK v) ==>
  ?m q. exec_block m C (scfg_bypass_block a b bb) t = q /\ scfg_result r q
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> fs[terminates_def]) >>
  drule_all scfg_exec_endpoint >> strip_tac >>
  `bb_well_formed bb` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, wf_function_bb_well_formed] >>
  drule_all scfg_bypass_iprefix_forward >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  `frame_reach C fn s0 i u` by (drule_all scfg_iprefix_frame_reach >> simp[]) >>
  `i.inst_opcode <> PHI` by
    (qpat_assum `scfg_iprefix C bb s u` (mp_tac o MATCH_MP scfg_iprefix_index) >> strip_tac >>
     `EVERY (\j. j.inst_opcode <> PHI)
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
     fs[EVERY_EL, get_instruction_def] >>
     first_x_assum (qspec_then
       `u.vs_inst_idx - phi_prefix_length bb.bb_instructions` mp_tac) >>
     simp[LENGTH_DROP, EL_DROP]) >>
  drule_all scfg_bypass_step_result >>
  disch_then (qspec_then `k` assume_tac) >>
  `get_instruction (scfg_bypass_block a b bb) w.vs_inst_idx = SOME
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) u.vs_current_bb i)` by
    (fs[scfg_bypass_instruction, scfg_bypass_aligned_def, scfg_ctrl_def] >>
     metis_tac[scfg_iprefix_current_bb]) >>
  (qpat_assum `z = r` (fn _ => suspend "nonOK") ORELSE suspend "halt")
QED

Resume scfg_bypass_exec_terminal_forward[nonOK]:
  qmatch_asmsub_abbrev_tac `scfg_result _ (step_inst k C j w)` >>
  `?m. exec_block m C (scfg_bypass_block a b bb) t = step_inst k C j w` by
    (irule scfg_iprefix_continue >> conj_tac
     >- (Cases_on `r` >> Cases_on `step_inst k C j w` >>
         gvs[scfg_result_def, terminates_def]) >>
     qexistsl_tac [`k`, `w`] >> simp[] >>
     Cases_on `r` >> Cases_on `step_inst k C j w` >>
     gvs[scfg_result_def, terminates_def] >> simp[Once exec_block_def]) >>
  metis_tac[]
QED

Resume scfg_bypass_exec_terminal_forward[halt]:
  qmatch_asmsub_abbrev_tac `scfg_result _ (step_inst k C j w)` >>
  `is_terminator j.inst_opcode` by
    (simp[Abbr `j`] >> metis_tac[scfg_bypass_image_opcode, is_terminator_def]) >>
  Cases_on `v.vs_halted` >> gvs[] >>
  Cases_on `step_inst k C j w` >> gvs[scfg_result_def] >>
  rename1 `step_inst k C j w = OK next` >>
  `next.vs_halted` by
    (qpat_x_assum `scfg_payload v next` mp_tac >>
     simp[scfg_payload_def] >> strip_tac >>
     qpat_x_assum `next = _` (fn th => once_rewrite_tac[th]) >>
     simp[scfg_ctrl_def]) >>
  `?m. exec_block m C (scfg_bypass_block a b bb) t = Halt next` by
    (irule scfg_exec_endpoint_reconstruct >> simp[] >>
     qexistsl_tac [`j`, `k`, `w`] >> simp[]) >>
  metis_tac[scfg_result_def]
QED
Finalise scfg_bypass_exec_terminal_forward

Theorem scfg_bypass_exec_terminal_backward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
  scfg_bypass_aligned a b s t /\
  exec_block k C (scfg_bypass_block a b bb) t = r /\
  terminates r /\ (!v. r <> OK v) ==>
  ?m q. exec_block m C bb s = q /\ scfg_result q r
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> fs[terminates_def]) >>
  drule_all scfg_exec_endpoint >> strip_tac >>
  `bb_well_formed (scfg_bypass_block a b bb)` by
    metis_tac[scfg_bypass_block_wf, scfg_bypass_old_static, scfg_static_wf,
      wf_function_bb_well_formed] >>
  `phi_prefix_length (scfg_bypass_block a b bb).bb_instructions <= t.vs_inst_idx` by
    fs[scfg_bypass_phi_prefix_length, scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `?w. scfg_iprefix C bb s w /\ scfg_bypass_aligned a b w u` by
    (irule scfg_bypass_iprefix_backward >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `C` >> simp[ctx_bisim_refl]) >>
  `?j. get_instruction bb w.vs_inst_idx = SOME j /\
    i = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) w.vs_current_bb j` by
    (fs[scfg_bypass_instruction, scfg_bypass_aligned_def, scfg_ctrl_def] >>
     Cases_on `get_instruction bb w.vs_inst_idx` >> gvs[] >>
     metis_tac[scfg_iprefix_current_bb]) >>
  `frame_reach C fn s0 j w` by (drule_all scfg_iprefix_frame_reach >> simp[]) >>
  `j.inst_opcode <> PHI` by
    (qpat_assum `scfg_iprefix C bb s w` (mp_tac o MATCH_MP scfg_iprefix_index) >> strip_tac >>
     `bb_well_formed bb` by
       metis_tac[scfg_bypass_old_static, scfg_static_wf, wf_function_bb_well_formed] >>
     `EVERY (\j. j.inst_opcode <> PHI)
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
     fs[EVERY_EL, get_instruction_def] >>
     first_x_assum (qspec_then
       `w.vs_inst_idx - phi_prefix_length bb.bb_instructions` mp_tac) >>
     simp[LENGTH_DROP, EL_DROP]) >>
  drule_all scfg_bypass_step_result >>
  disch_then (qspec_then `k` assume_tac) >>
  (qpat_assum `z = r` (fn _ => suspend "nonOK") ORELSE suspend "halt")
QED

Resume scfg_bypass_exec_terminal_backward[nonOK]:
  `?m. exec_block m C bb s = step_inst k C j w` by
    (irule scfg_iprefix_continue >> conj_tac
     >- (Cases_on `r` >> Cases_on `step_inst k C j w` >>
         gvs[scfg_result_def, terminates_def]) >>
     qexistsl_tac [`k`, `w`] >> simp[] >>
     Cases_on `r` >> Cases_on `step_inst k C j w` >>
     gvs[scfg_result_def, terminates_def] >> simp[Once exec_block_def]) >>
  metis_tac[]
QED

Resume scfg_bypass_exec_terminal_backward[halt]:
  `is_terminator j.inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  Cases_on `step_inst k C j w` >> gvs[scfg_result_def] >>
  rename1 `step_inst k C j w = OK next` >>
  `next.vs_halted` by
    (qpat_x_assum `scfg_payload next v` mp_tac >>
     simp[scfg_payload_def] >> strip_tac >>
     qpat_x_assum `v = _` (fn th => qpat_x_assum `v.vs_halted` mp_tac >> once_rewrite_tac[th]) >>
     simp[scfg_ctrl_def]) >>
  `?m. exec_block m C bb s = Halt next` by
    (irule scfg_exec_endpoint_reconstruct >> simp[] >>
     qexistsl_tac [`j`, `k`, `w`] >> simp[]) >>
  metis_tac[scfg_result_def]
QED
Finalise scfg_bypass_exec_terminal_backward

Theorem scfg_bypass_run_block_terminal_forward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k C bb s = r /\ terminates r /\ (!v. r <> OK v) ==>
  ?m q. run_block m C (scfg_bypass_block a b bb) t = q /\ scfg_result r q
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> fs[terminates_def]) >>
  drule_all scfg_run_block_entry >> strip_tac >>
  drule_all scfg_bypass_rooted_entry_forward >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `phi_prefix_length bb.bb_instructions <= x.vs_inst_idx` by simp[] >>
  drule_all scfg_bypass_exec_terminal_forward >> strip_tac >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >> disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  drule_all scfg_enters_block_run_block >>
  disch_then (qspecl_then [`m`, `C`] assume_tac) >> metis_tac[]
QED

Theorem scfg_bypass_run_block_terminal_backward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k C (scfg_bypass_block a b bb) t = r /\ terminates r /\ (!v. r <> OK v) ==>
  ?m q. run_block m C bb s = q /\ scfg_result q r
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> fs[terminates_def]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >> disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  drule_all scfg_run_block_entry >> disch_then (qx_choose_then `y` strip_assume_tac) >>
  drule_all scfg_bypass_rooted_entry_backward >> disch_then (qx_choose_then `x` strip_assume_tac) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `phi_prefix_length bb.bb_instructions <= x.vs_inst_idx` by simp[] >>
  drule_all scfg_bypass_exec_terminal_backward >> strip_tac >>
  qpat_x_assum `enters_block fn' t y` kall_tac >>
  drule_all scfg_enters_block_run_block >>
  disch_then (qspecl_then [`m`, `C`] assume_tac) >> metis_tac[]
QED
