(* Rooted whole-function transport for a contracted chain. *)
Theory simplifyCfgMergeSemantics
Ancestors
  simplifyCfgMergeRuns simplifyCfgMergeSegment simplifyCfgMergeEntry
  simplifyCfgMergePaths simplifyCfgMergeExec simplifyCfgMergeClosure
  simplifyCfgFixupStatic simplifyCfgAvailability
  simplifyCfgFragments simplifyCfgFramePrefixes simplifyCfgStaticInterface
  simplifyCfgControl simplifyCfgControlExec simplifyCfgSimTools venomExecSemantics venomExecProofs
  contextCodegenRel o1PassLift venomState venomWf venomInst cfgTransform
  simplifyCfgDefs passSimulationDefs list

Theorem scfg_chain_rooted_incoming:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  (case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb)
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by
    metis_tac[scfg_chain_old_wf, scfg_chain_hyp_def, scfg_normalized_static,
      scfg_static_inst_wf] >>
  drule_all scfg_bprefix_incoming >> strip_tac
  >- gvs[fn_entry_state_def] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  simp[] >> metis_tac[]
QED

Theorem scfg_chain_exit_ctrl:
  scfg_chain_exit a b s t ==>
  t = scfg_ctrl s.vs_current_bb
    (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 s
Proof
  simp[scfg_chain_exit_def, scfg_payload_def] >> rpt strip_tac >> gvs[]
QED

Theorem scfg_chain_rooted_enter:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  enters_block (scfg_chain fn a b) t t1 ==>
  ?s1. enters_block fn s s1 /\
    (scfg_chain_segment a b s1 t1 \/ scfg_chain_splice a s1 t1) /\
    (!i. active_inst fn i s1 ==> frame_reach C fn s0 i s1)
Proof
  strip_tac >>
  `s.vs_current_bb <> b.bb_label` by fs[scfg_chain_exit_def] >>
  drule_all scfg_chain_rooted_incoming >> strip_tac >>
  drule scfg_chain_exit_ctrl >> strip_tac >>
  drule_all scfg_chain_enters_block >> strip_tac >>
  `?s1. enters_block fn s s1 /\
    t1 = scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s1.vs_inst_idx s1` by metis_tac[] >>
  qexists_tac `s1` >> simp[] >> conj_tac
  >- (drule_all scfg_chain_enters_segment >> strip_tac >>
      fs[enters_block_def] >> gvs[]) >>
  metis_tac[scfg_bprefix_enter_reach]
QED

Theorem scfg_chain_block_backward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  run_block n C bt t = q /\ terminates q ==>
  ?r.
    ((?k. run_block k C bb s = r /\
        (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
     (?k1 k2 x. bb.bb_label = a.bb_label /\
        run_block k1 C bb s = OK x /\ ~x.vs_halted /\
        x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
    scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  strip_tac >>
  qspecl_then [`t`, `bt.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis t bt.bb_instructions = OK v` >>
      `enters_block (scfg_chain fn a b) t
        (v with vs_inst_idx := phi_prefix_length bt.bb_instructions)` by
        (simp[enters_block_def] >> metis_tac[]) >>
      drule_all scfg_chain_rooted_enter >> strip_tac >>
      `~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb` by
        (qpat_assum `enters_block fn s s1`
           (strip_assume_tac o REWRITE_RULE[enters_block_def]) >> gvs[] >>
         qpat_assum `eval_phis s _ = OK _`
           (mp_then Any assume_tac eval_phis_preserves_halted) >>
         qpat_assum `eval_phis s _ = OK _`
           (mp_then Any assume_tac eval_phis_preserves_current_bb) >> simp[]) >>
      `exec_block n C bt
        (v with vs_inst_idx := phi_prefix_length bt.bb_instructions) = q` by
        fs[run_block_def] >>
      `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
      `lookup_block
        (v with vs_inst_idx := phi_prefix_length bt.bb_instructions).vs_current_bb
        (scfg_chain fn a b).fn_blocks = SOME bt` by
        (simp[] >> metis_tac[eval_phis_preserves_current_bb]) >>
      qpat_assum `exec_block n C bt _ = q`
        (mp_then Any mp_tac scfg_chain_exec_backward) >>
      disch_then drule >> disch_then drule >>
      disch_then (qspec_then `s1` mp_tac) >>
      disch_then drule >> simp[] >> strip_tac >>
      qexists_tac `r` >> simp[] >>
      fs[enters_block_def] >> gvs[] >>
      simp[run_block_def] >> metis_tac[]) >>
  gvs[run_block_def, terminates_def]
QED

Theorem scfg_chain_exit_lookup:
  scfg_chain_hyp fn a b /\ scfg_chain_exit a b s t /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb
Proof
  strip_tac >> drule scfg_chain_lookup_eq >>
  disch_then (qspec_then `t.vs_current_bb` assume_tac) >>
  fs[scfg_chain_exit_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]
QED

Theorem scfg_chain_block_prefix_backward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  run_block n C bt t = OK v /\ ~v.vs_halted ==>
  ?u. scfg_bprefix C fn s u /\ ~u.vs_halted /\ scfg_chain_exit a b u v
Proof
  strip_tac >> drule_all scfg_chain_exit_lookup >> strip_tac >>
  `terminates (OK v)` by simp[terminates_def] >>
  drule_all scfg_chain_block_backward >> strip_tac >>
  `?u. r = OK u` by
    (Cases_on `r` >> fs[scfg_result_def]) >>
  qpat_x_assum `r = OK u` SUBST_ALL_TAC >>
  `scfg_chain_exit a b u v` by metis_tac[exec_result_11] >>
  `~u.vs_halted` by
    (qpat_assum `scfg_chain_exit a b u v`
       (mp_then Any mp_tac scfg_chain_exit_ctrl) >>
     disch_then (fn th => qpat_x_assum `~v.vs_halted` mp_tac >>
       once_rewrite_tac[th]) >> simp[scfg_ctrl_def]) >>
  qexists_tac `u` >> simp[]
  >- metis_tac[scfg_bprefix_single] >>
  `lookup_block x.vs_current_bb fn.fn_blocks = SOME b` by
    fs[scfg_chain_hyp_def] >>
  metis_tac[scfg_bprefix_single, scfg_bprefix_trans]
QED

Theorem scfg_chain_bprefix_backward:
  !C g t v. scfg_bprefix C g t v ==>
  !fn a b s0 s. g = scfg_chain fn a b /\
    scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
    scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t ==>
    ?u. scfg_bprefix C fn s u /\ ~u.vs_halted /\ scfg_chain_exit a b u v
Proof
  ho_match_mp_tac scfg_bprefix_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `s` >> simp[scfg_bprefix_rules]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all scfg_chain_block_prefix_backward >>
  disch_then (qx_choose_then `u1` strip_assume_tac) >>
  `scfg_bprefix C fn s0 u1` by metis_tac[scfg_bprefix_trans] >>
  first_x_assum (qspecl_then [`fn`, `a`, `b`, `s0`] mp_tac) >>
  disch_then (qspec_then `u1` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[scfg_bprefix_trans]
QED

Theorem scfg_chain_initial_exit:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 ==>
  scfg_chain_exit a b s0 s0
Proof
  strip_tac >>
  `first_block_no_preds fn` by
    metis_tac[scfg_chain_hyp_def, scfg_normalized_static, scfg_static_first_no_preds] >>
  `fn_entry_label fn <> SOME b.bb_label` by
    metis_tac[simplifyCfgMergeStaticTheory.scfg_merge_not_entry, scfg_chain_hyp_def] >>
  fs[scfg_chain_exit_def, fn_entry_state_def] >> metis_tac[]
QED

Theorem scfg_chain_rooted_observation:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  eval_phis t bt.bb_instructions = OK v /\
  scfg_iprefix C bt (v with vs_inst_idx := phi_prefix_length bt.bb_instructions) w /\
  get_instruction bt w.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI ==>
  ?u. frame_reach C fn s0 i u /\ scfg_payload u w /\
    mem_corr i u i w /\ call_corr i u i w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_exit_lookup >> strip_tac >>
  `enters_block (scfg_chain fn a b) t
    (v with vs_inst_idx := phi_prefix_length bt.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  drule_all scfg_chain_rooted_enter >>
  disch_then (qx_choose_then `s1` (map_every assume_tac o CONJUNCTS)) >>
  `~s1.vs_halted /\ s1.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `enters_block fn s s1`
       (strip_assume_tac o REWRITE_RULE[enters_block_def]) >> gvs[] >>
     qpat_assum `eval_phis s _ = OK _`
       (mp_then Any assume_tac eval_phis_preserves_halted) >>
     qpat_assum `eval_phis s _ = OK _`
       (mp_then Any assume_tac eval_phis_preserves_current_bb) >> simp[]) >>
  irule scfg_chain_iprefix_observation >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`a`, `b`, `bb`] >>
  goal_assum (drule_at (Pat `scfg_iprefix _ _ _ _`)) >> simp[] >>
  metis_tac[eval_phis_preserves_current_bb]
QED

Theorem scfg_wf_prefix_instruction_nonphi:
  wf_function fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_iprefix C bb (v with vs_inst_idx := phi_prefix_length bb.bb_instructions) w /\
  get_instruction bb w.vs_inst_idx = SOME i ==>
  i.inst_opcode <> PHI
Proof
  strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed, lookup_block_MEM] >>
  `EVERY (\i. i.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
  drule scfg_iprefix_index >> simp[] >> strip_tac >>
  fs[get_instruction_def, EVERY_EL] >>
  first_x_assum (qspec_then `w.vs_inst_idx - phi_prefix_length bb.bb_instructions` mp_tac) >>
  simp[LENGTH_DROP, EL_DROP]
QED

Theorem scfg_chain_frame_sim:
  scfg_chain_hyp fn a b ==> frame_sim L C C fn (scfg_chain fn a b)
Proof
  strip_tac >> simp[frame_sim_def] >> qx_genl_tac [`s0`, `j`, `w`] >> strip_tac >>
  `wf_function (scfg_chain fn a b)` by metis_tac[scfg_chain_wf] >>
  drule_all scfg_frame_reach_decompose >>
  disch_then (qx_choosel_then [`s`, `bb`, `v`, `e`] strip_assume_tac) >>
  `scfg_chain_exit a b s0 s0` by metis_tac[scfg_chain_initial_exit] >>
  `~s0.vs_halted` by fs[fn_entry_state_def] >>
  `?u. scfg_bprefix C fn s0 u /\ ~u.vs_halted /\ scfg_chain_exit a b u s` by
    (irule scfg_chain_bprefix_backward >>
     goal_assum (drule_at Any) >> simp[scfg_bprefix_rules] >>
     conj_tac >- (qexists_tac `s0` >> simp[scfg_bprefix_rules]) >>
     qexists_tac `s0` >> simp[]) >>
  `j.inst_opcode <> PHI` by
    (irule scfg_wf_prefix_instruction_nonphi >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  drule_all scfg_chain_rooted_observation >>
  disch_then (qx_choose_then `u1` strip_assume_tac) >>
  qexistsl_tac [`j`, `u1`] >> simp[]
QED
