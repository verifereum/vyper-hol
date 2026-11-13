(* Non-error execution of one transformed block corresponds to one source
   block, or to the remainder of A followed by the genuine entry to B. *)
Theory simplifyCfgMergeRuns
Ancestors
  simplifyCfgMergeSegment simplifyCfgMergePaths simplifyCfgMergeExec
  simplifyCfgStaticInterface simplifyCfgSimTools simplifyCfgControlExec simplifyCfgControl
  simplifyCfgFragments passSimulationProps contextCodegenRel venomExecSemantics
  venomExecProofs venomWf venomInst venomState o1PassLift simplifyCfgDefs
  cfgTransform cfgHelpers list rich_list passSimulationDefs

Theorem scfg_chain_segment_terminator_source:
  scfg_chain_hyp fn a b /\ scfg_chain_segment a b s t /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode ==>
  s.vs_current_bb <> a.bb_label
Proof
  strip_tac >> strip_tac >>
  `a.bb_label <> b.bb_label` by metis_tac[scfg_chain_distinct_labels] >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  `wf_function fn` by metis_tac[scfg_chain_old_wf] >>
  `lookup_block a.bb_label fn.fn_blocks = SOME a` by fs[scfg_chain_hyp_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  fs[active_inst_def] >>
  `bb = a` by metis_tac[MEM_lookup_block, optionTheory.SOME_11] >> gvs[] >>
  `s.vs_inst_idx < LENGTH a.bb_instructions - 1` by
    (fs[scfg_chain_segment_def] >>
     Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT]) >>
  metis_tac[wf_non_terminator_prefix]
QED

Theorem scfg_terminator_jump:
  is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\ u = jump_to u.vs_current_bb s
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  gvs[is_terminator_def] >>
  fs[Once step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[jump_to_def]
QED

Theorem scfg_active_terminator_last:
  wf_function fn /\ active_inst fn i s /\ is_terminator i.inst_opcode ==>
  ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
       bb.bb_instructions <> [] /\ i = LAST bb.bb_instructions
Proof
  strip_tac >> fs[active_inst_def] >> qexists_tac `bb` >> simp[] >>
  `~(s.vs_inst_idx < LENGTH bb.bb_instructions - 1)` by
    metis_tac[wf_non_terminator_prefix] >>
  `s.vs_inst_idx = LENGTH bb.bb_instructions - 1` by decide_tac >>
  Cases_on `bb.bb_instructions` >> gvs[LAST_EL]
QED

Theorem scfg_chain_segment_terminator_destination:
  scfg_chain_hyp fn a b /\ scfg_chain_segment a b s t /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  step_inst k C i s = OK u /\ ~u.vs_halted ==>
  u.vs_current_bb <> b.bb_label
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  `wf_function fn` by metis_tac[scfg_chain_old_wf] >>
  `inst_wf i` by
    (irule active_inst_wf >> qexistsl_tac [`fn`, `s`] >> simp[] >>
     metis_tac[scfg_chain_hyp_def, scfg_normalized_static, scfg_static_inst_wf]) >>
  `i.inst_opcode <> INVOKE` by (Cases_on `i.inst_opcode` >> fs[is_terminator_def]) >>
  `step_inst_base i s = OK u` by fs[Once step_inst_def] >>
  `MEM u.vs_current_bb (get_successors i)` by
    metis_tac[step_inst_base_term_succs] >>
  drule_all scfg_active_terminator_last >> strip_tac >>
  `fn_cfg_edge fn s.vs_current_bb u.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> qexists_tac `bb` >>
     Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub]) >>
  metis_tac[scfg_chain_incoming, scfg_chain_segment_terminator_source]
QED

Theorem scfg_chain_segment_terminator_exit:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_chain_segment a b s t /\ frame_reach C fn s0 i s /\
  is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\ ~u.vs_halted ==>
  ?v. step_inst k C i t = OK v /\ scfg_chain_exit a b u v
Proof
  strip_tac >>
  `u.vs_current_bb <> b.bb_label` by
    metis_tac[scfg_chain_segment_terminator_destination] >>
  drule_all scfg_terminator_jump >> strip_tac >>
  `a.bb_label <> b.bb_label` by metis_tac[scfg_chain_distinct_labels] >>
  `step_inst k C i s = OK (jump_to u.vs_current_bb s)` by metis_tac[] >>
  drule_all scfg_chain_segment_branch >> strip_tac >>
  qexists_tac `jump_to u.vs_current_bb t` >> metis_tac[]
QED

Theorem scfg_chain_run_right:
  scfg_chain_hyp fn a b ==>
  run_block k C b (jump_to b.bb_label s) =
  exec_block k C b (jump_to b.bb_label s)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    metis_tac[scfg_chain_no_phis, no_phis_def] >>
  simp[run_block_def, eval_phis_no_phis, no_phis_phi_prefix_length_zero,
    jump_to_def]
QED

Theorem scfg_chain_splice_exec:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_chain_splice a s t /\ ~s.vs_halted /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  exec_block k C a s = OK (jump_to b.bb_label s)
Proof
  strip_tac >>
  `frame_reach C fn s0 (LAST a.bb_instructions) s` by
    metis_tac[scfg_chain_splice_active] >>
  `get_instruction a s.vs_inst_idx = SOME (LAST a.bb_instructions)` by
    (fs[scfg_chain_splice_def, get_instruction_def] >>
     `a.bb_instructions <> []` by metis_tac[scfg_chain_blocks_nonempty] >>
     Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT, LAST_EL]) >>
  `is_terminator (LAST a.bb_instructions).inst_opcode` by
    (drule scfg_chain_transfer_shape >> strip_tac >> simp[is_terminator_def]) >>
  `step_inst k C (LAST a.bb_instructions) s = OK (jump_to b.bb_label s)` by
    metis_tac[scfg_chain_transfer_step] >>
  simp[Once exec_block_def, jump_to_def]
QED

Theorem scfg_chain_source_prepend:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
  ((?n. exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = r /\
       (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
   (?n m x. bb.bb_label = a.bb_label /\
       exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r)) /\
  terminates r ==>
  (?n. exec_block n C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
  (?n m x. bb.bb_label = a.bb_label /\ exec_block n C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r)
Proof
  strip_tac
  >- (disj1_tac >>
      `?m. exec_block m C bb s = r` by
        (irule scfg_istep_continue >> conj_tac
         >- (Cases_on `r` >> gvs[terminates_def]) >> metis_tac[]) >>
      metis_tac[])
  >- (disj1_tac >>
      `?m. exec_block m C bb s = r` by
        (irule scfg_istep_continue >> conj_tac
         >- (Cases_on `r` >> gvs[terminates_def]) >> metis_tac[]) >>
      metis_tac[]) >>
  disj2_tac >>
  `?m. exec_block m C bb s = OK x` by
    (irule scfg_istep_continue >> metis_tac[exec_result_distinct]) >>
  metis_tac[]
QED

Theorem scfg_chain_source_splice:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_chain_splice a s t /\ ~s.vs_halted /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block n C b (jump_to b.bb_label s) = r ==>
  ?k m x. bb.bb_label = a.bb_label /\ exec_block k C bb s = OK x /\
    ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r
Proof
  strip_tac >>
  `bb = a` by (fs[scfg_chain_splice_def, scfg_chain_hyp_def] >> gvs[]) >>
  fs[] >>
  `exec_block 0 C a s = OK (jump_to b.bb_label s)` by
    metis_tac[scfg_chain_splice_exec] >>
  `run_block n C b (jump_to b.bb_label s) = r` by
    metis_tac[scfg_chain_run_right] >>
  qexistsl_tac [`0`, `n`, `jump_to b.bb_label s`] >> simp[jump_to_def]
QED

Theorem scfg_chain_source_normalize:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  ?w bw. scfg_chain_segment a b w t /\ ~w.vs_halted /\
    lookup_block w.vs_current_bb fn.fn_blocks = SOME bw /\
    (!i. active_inst fn i w ==> frame_reach C fn s0 i w) /\
    (!r.
      ((?k. exec_block k C bw w = r /\
          (bw.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
       (?k m x. bw.bb_label = a.bb_label /\ exec_block k C bw w = OK x /\
          ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r)) ==>
      (?k. exec_block k C bb s = r /\
          (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
      (?k m x. bb.bb_label = a.bb_label /\ exec_block k C bb s = OK x /\
          ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r))
Proof
  strip_tac
  >- (qexistsl_tac [`s`, `bb`] >> simp[]) >>
  drule_all scfg_chain_splice_rooted >> strip_tac >>
  qexistsl_tac [`jump_to b.bb_label s`, `b`] >>
  `lookup_block b.bb_label fn.fn_blocks = SOME b` by fs[scfg_chain_hyp_def] >>
  `a.bb_label <> b.bb_label` by metis_tac[scfg_chain_distinct_labels] >>
  simp[jump_to_def] >> rpt strip_tac >> disj2_tac >>
  irule scfg_chain_source_splice >>
  metis_tac[jump_to_def]
QED

Theorem scfg_chain_segment_terminator_back:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  scfg_chain_segment a b s t /\ frame_reach C fn s0 i s /\
  is_terminator i.inst_opcode /\ step_inst k C i t = q ==>
  ?r. step_inst k C i s = r /\ scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  strip_tac >>
  `scfg_payload s t` by metis_tac[scfg_chain_segment_payload] >>
  `scfg_result (step_inst k C i s) q` by metis_tac[scfg_payload_step] >>
  qexists_tac `step_inst k C i s` >> simp[] >> rpt strip_tac >>
  `u = jump_to u.vs_current_bb s` by metis_tac[scfg_terminator_jump] >>
  `~u.vs_halted` by
    (qpat_x_assum `u = jump_to _ s` (fn th => once_rewrite_tac[th]) >>
     simp[jump_to_def]) >>
  drule_all scfg_chain_segment_terminator_exit >> metis_tac[exec_result_11]
QED

Theorem scfg_result_terminates[local]:
  scfg_result r q ==> (terminates r <=> terminates q)
Proof
  Cases_on `r` >> Cases_on `q` >> simp[scfg_result_def, terminates_def]
QED

Theorem scfg_chain_terminal_exec_back:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  scfg_chain_segment a b s t /\ frame_reach C fn s0 i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst k C i t = q /\ (!v. q <> OK v) ==>
  ?r. exec_block k C bb s = r /\ (!v. r <> OK v) /\ scfg_result r q
Proof
  strip_tac >>
  `scfg_payload s t` by metis_tac[scfg_chain_segment_payload] >>
  `scfg_result (step_inst k C i s) q` by metis_tac[scfg_payload_step] >>
  Cases_on `step_inst k C i s` >> Cases_on `q` >>
  gvs[scfg_result_def] >>
  simp[Once exec_block_def, scfg_result_def] >>
  simp[Once exec_block_def, scfg_result_def]
QED

Theorem scfg_chain_branch_exec_back:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  scfg_chain_segment a b s t /\ frame_reach C fn s0 i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  is_terminator i.inst_opcode /\ step_inst k C i t = OK v ==>
  ?u. exec_block k C bb s = OK u /\ bb.bb_label <> a.bb_label /\
      scfg_result (OK u) (OK v) /\ scfg_chain_exit a b u v
Proof
  strip_tac >> drule_all scfg_chain_segment_terminator_back >> strip_tac >>
  Cases_on `r` >> gvs[scfg_result_def] >>
  rename1 `step_inst k C i s = OK u` >>
  `u = jump_to u.vs_current_bb s` by metis_tac[scfg_terminator_jump] >>
  `~u.vs_halted` by
    (qpat_x_assum `u = jump_to _ s` (fn th => once_rewrite_tac[th]) >>
     simp[jump_to_def]) >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  qexists_tac `u` >> simp[Once exec_block_def, scfg_result_def] >>
  metis_tac[scfg_chain_segment_terminator_source]
QED

Theorem scfg_step_terminates_nonphi[local]:
  terminates (step_inst k C i s) ==> i.inst_opcode <> PHI
Proof
  strip_tac >> strip_tac >> Cases_on `i` >>
  gvs[step_inst_def, step_inst_base_def, terminates_def]
QED

Theorem scfg_chain_exec_backward_distance:
  !d fn a b C s0 s t bb bt n q.
  LENGTH bt.bb_instructions - t.vs_inst_idx = d /\
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  exec_block n C bt t = q /\ terminates q ==>
  ?r.
    ((?k. exec_block k C bb s = r /\
        (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
     (?k1 k2 x. bb.bb_label = a.bb_label /\
        exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
        x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
    scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  completeInduct_on `d` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_source_normalize >> strip_tac >>
  qpat_x_assum `!r. _ ==> _` (irule_at (Pos hd)) >>
  qpat_x_assum `scfg_chain_segment a b s t \/ _` kall_tac >>
  qpat_x_assum `lookup_block s.vs_current_bb _ = _` kall_tac >>
  qpat_x_assum `!i. active_inst fn i s ==> _` kall_tac >>
  qpat_x_assum `~s.vs_halted` kall_tac >>
  qpat_x_assum `exec_block n C bt t = q`
    (mp_tac o ONCE_REWRITE_RULE [exec_block_def]) >>
  Cases_on `get_instruction bt t.vs_inst_idx` >> simp[]
  >- (strip_tac >> gvs[terminates_def]) >>
  rename1 `get_instruction bt t.vs_inst_idx = SOME i` >>
  Cases_on `step_inst n C i t` >> simp[]
  >- suspend "ok" >>
  strip_tac >> pop_assum (SUBST_ALL_TAC o SYM) >>
  fs[terminates_def] >>
  `i.inst_opcode <> PHI` by
    (irule scfg_step_terminates_nonphi >>
     qexistsl_tac [`C`, `n`, `t`] >> simp[terminates_def]) >>
  `get_instruction bw w.vs_inst_idx = SOME i` by
    (irule scfg_chain_segment_instruction_inverse >> metis_tac[]) >>
  `active_inst fn i w` by
    (irule scfg_lookup_active >> qexistsl_tac [`w`, `bw`] >>
     metis_tac[lookup_block_member_label]) >>
  `frame_reach C fn s0 i w` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `step_inst n C i t = z` >>
  `!v. z <> OK v` by simp[Abbr `z`] >>
  drule_all scfg_chain_terminal_exec_back >> strip_tac >>
  qexists_tac `r` >> simp[Abbr `z`] >> metis_tac[]
QED

Resume scfg_chain_exec_backward_distance[ok]:
  `i.inst_opcode <> PHI` by metis_tac[scfg_step_OK_nonphi] >>
  `get_instruction bw w.vs_inst_idx = SOME i` by
    (irule scfg_chain_segment_instruction_inverse >> metis_tac[]) >>
  `active_inst fn i w` by
    (irule scfg_lookup_active >> qexistsl_tac [`w`, `bw`] >>
     metis_tac[lookup_block_member_label]) >>
  `frame_reach C fn s0 i w` by metis_tac[] >>
  `~t.vs_halted` by
    (drule scfg_chain_segment_payload >> simp[scfg_payload_def] >> strip_tac >>
     qpat_x_assum `t = scfg_ctrl _ _ _ w` (fn th => once_rewrite_tac[th]) >>
     simp[scfg_ctrl_def]) >>
  Cases_on `is_terminator i.inst_opcode`
  >- (`v = jump_to v.vs_current_bb t` by metis_tac[scfg_terminator_jump] >>
      `~v.vs_halted` by
        (qpat_x_assum `v = jump_to _ t` (fn th => once_rewrite_tac[th]) >>
         simp[jump_to_def]) >>
      simp[] >> strip_tac >> pop_assum (SUBST_ALL_TAC o SYM) >>
      drule_all scfg_chain_branch_exec_back >> strip_tac >>
      qexists_tac `OK u` >> simp[] >> qexists_tac `n` >> simp[]) >>
  simp[] >> strip_tac >>
  drule_all scfg_chain_segment_rooted_advance >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  `v.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `LENGTH bt.bb_instructions - SUC t.vs_inst_idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`fn`, `a`, `b`, `C`, `s0`,
    `u with vs_inst_idx := SUC w.vs_inst_idx`,
    `v with vs_inst_idx := SUC t.vs_inst_idx`, `bw`, `bt`, `n`, `q`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `r` (map_every assume_tac o CONJUNCTS)) >>
  qexists_tac `r` >> simp[] >>
  `terminates r` by metis_tac[scfg_result_terminates] >>
  drule_all (SRULE [] scfg_chain_source_prepend) >> simp[]
QED

Finalise scfg_chain_exec_backward_distance


Theorem scfg_chain_exec_backward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  exec_block n C bt t = q /\ terminates q ==>
  ?r.
    ((?k. exec_block k C bb s = r /\
        (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
     (?k1 k2 x. bb.bb_label = a.bb_label /\
        exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
        x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
    scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  strip_tac >> irule scfg_chain_exec_backward_distance >> simp[] >>
  metis_tac[]
QED

Theorem scfg_chain_source_splice_cancel:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_chain_splice a s t /\ ~s.vs_halted /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ((?k. exec_block k C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?k1 k2 x. bb.bb_label = a.bb_label /\
       exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) ==>
  ?k. exec_block k C b (jump_to b.bb_label s) = r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bb = a` by (fs[scfg_chain_splice_def, scfg_chain_hyp_def] >> gvs[]) >>
  qpat_x_assum `bb = a` SUBST_ALL_TAC >>
  `!k. exec_block k C a s = OK (jump_to b.bb_label s)` by
    (gen_tac >> irule scfg_chain_splice_exec >> metis_tac[]) >>
  qpat_x_assum `(?k. _) \/ _` strip_assume_tac >> gvs[] >>
  metis_tac[scfg_chain_run_right]
QED

Theorem scfg_chain_source_normalize_forward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((?k. exec_block k C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?k1 k2 x. bb.bb_label = a.bb_label /\
       exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) ==>
  ?w bw. scfg_chain_segment a b w t /\ ~w.vs_halted /\
    lookup_block w.vs_current_bb fn.fn_blocks = SOME bw /\
    (!i. active_inst fn i w ==> frame_reach C fn s0 i w) /\
    ((?k. exec_block k C bw w = r /\
         (bw.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
     (?k1 k2 x. bw.bb_label = a.bb_label /\
         exec_block k1 C bw w = OK x /\ ~x.vs_halted /\
         x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `scfg_chain_segment a b s t \/ _` strip_assume_tac
  >- (qexistsl_tac [`s`, `bb`] >> simp[]) >>
  drule_all scfg_chain_source_splice_cancel >> strip_tac >>
  drule_all scfg_chain_splice_rooted >> strip_tac >>
  qexistsl_tac [`jump_to b.bb_label s`, `b`] >>
  `a.bb_label <> b.bb_label` by metis_tac[scfg_chain_distinct_labels] >>
  `lookup_block b.bb_label fn.fn_blocks = SOME b` by fs[scfg_chain_hyp_def] >>
  simp[jump_to_def] >> metis_tac[jump_to_def]
QED

Theorem scfg_chain_source_head:
  ((?k. exec_block k C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?k1 k2 x. bb.bb_label = a.bb_label /\
       exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
  terminates r ==>
  ?k i z. get_instruction bb s.vs_inst_idx = SOME i /\
    step_inst k C i s = z /\ terminates z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?k z. exec_block k C bb s = z /\ terminates z` by
    (qpat_x_assum `(?k. _) \/ _` strip_assume_tac >>
     goal_assum (drule_at (Pos hd)) >> simp[terminates_def]) >>
  qpat_x_assum `(?k. _) \/ _` kall_tac >>
  qpat_x_assum `terminates r` kall_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [exec_block_def]) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[]
  >- (strip_tac >> gvs[terminates_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `step_inst k C i s` >> simp[] >>
  rpt strip_tac >> gvs[terminates_def] >>
  qexists_tac `k` >> simp[]
QED

Theorem scfg_exec_nonerror_unique:
  exec_block k C bb s = r /\ exec_block n C bb s = q /\
  terminates r /\ terminates q ==> r = q
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> gvs[terminates_def]) >>
  `!e. q <> Error e` by (Cases_on `q` >> gvs[terminates_def]) >>
  `exec_block (MAX k n) C bb s = r` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  `exec_block (MAX k n) C bb s = q` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  metis_tac[]
QED

Theorem scfg_chain_source_stop:
  ((?k. exec_block k C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?k1 k2 x. bb.bb_label = a.bb_label /\
       exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
  terminates r /\ exec_block n C bb s = z /\ terminates z /\
  (bb.bb_label <> a.bb_label \/ (!u. z <> OK u)) ==> r = z
Proof
  `!x. terminates (OK x)` by simp[terminates_def] >>
  strip_tac >> metis_tac[scfg_exec_nonerror_unique]
QED

Theorem scfg_chain_source_cancel:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
  ((?n. exec_block n C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
   (?n m x. bb.bb_label = a.bb_label /\ exec_block n C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r)) /\
  terminates r ==>
  (?n. exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = r /\
       (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
  (?n m x. bb.bb_label = a.bb_label /\
       exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block m C b x = r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `scfg_iprefix C bb s (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (cj 2 scfg_iprefix_rules) >> metis_tac[cj 1 scfg_iprefix_rules]) >>
  qpat_x_assum `(?n. _) \/ _` strip_assume_tac
  >- (`!e. r <> Error e` by (Cases_on `r` >> gvs[terminates_def]) >>
      drule_all scfg_iprefix_cancel >> metis_tac[])
  >- (`!e. r <> Error e` by (Cases_on `r` >> gvs[terminates_def]) >>
      drule_all scfg_iprefix_cancel >> metis_tac[]) >>
  `!e. OK x <> Error e` by simp[] >>
  drule_all scfg_iprefix_cancel >> metis_tac[]
QED

Theorem scfg_exec_terminal:
  get_instruction bb s.vs_inst_idx = SOME i /\
  step_inst k C i s = z /\ (!u. z <> OK u) ==>
  exec_block k C bb s = z
Proof
  strip_tac >> Cases_on `z` >> gvs[] >> simp[Once exec_block_def]
QED

Theorem scfg_chain_exec_forward_distance[local]:
  !d fn a b C s0 s t bb bt r.
  LENGTH bt.bb_instructions - t.vs_inst_idx = d /\
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((?k. exec_block k C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?k1 k2 x. bb.bb_label = a.bb_label /\
       exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
  terminates r ==>
  ?m q. exec_block m C bt t = q /\ scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  completeInduct_on `d` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_source_normalize_forward >>
  disch_then (qx_choose_then `w` (qx_choose_then `bw`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `scfg_chain_segment a b s t \/ _` kall_tac >>
  qpat_x_assum `lookup_block s.vs_current_bb _ = _` kall_tac >>
  qpat_x_assum `!i. active_inst fn i s ==> _` kall_tac >>
  qpat_x_assum `~s.vs_halted` kall_tac >>
  qpat_x_assum `(?k. exec_block k C bb s = r /\ _) \/ _` kall_tac >>
  drule_all scfg_chain_source_head >> strip_tac >>
  `i.inst_opcode <> PHI` by metis_tac[scfg_step_terminates_nonphi] >>
  `active_inst fn i w` by
    (irule scfg_lookup_active >> qexistsl_tac [`w`, `bw`] >>
     metis_tac[lookup_block_member_label]) >>
  `frame_reach C fn s0 i w` by metis_tac[] >>
  `get_instruction bt t.vs_inst_idx = SOME i` by
    metis_tac[scfg_chain_segment_instruction, optionTheory.SOME_11] >>
  Cases_on `?u. z = OK u`
  >- (pop_assum (qx_choose_then `u` SUBST_ALL_TAC) >> suspend "ok") >>
  `!u. z <> OK u` by metis_tac[] >>
  `exec_block k C bw w = z` by metis_tac[scfg_exec_terminal] >>
  `r = z` by metis_tac[scfg_chain_source_stop] >>
  `scfg_payload w t` by metis_tac[scfg_chain_segment_payload] >>
  `scfg_result z (step_inst k C i t)` by metis_tac[scfg_payload_step] >>
  `!u. step_inst k C i t <> OK u` by
    (qpat_x_assum `scfg_result z _` mp_tac >>
     qpat_x_assum `!u. z <> OK u` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `z` >> Cases_on `step_inst k C i t` >> simp[scfg_result_def]) >>
  qexistsl_tac [`k`, `step_inst k C i t`] >> simp[] >>
  metis_tac[scfg_exec_terminal]
QED

Resume scfg_chain_exec_forward_distance[ok]:
  Cases_on `is_terminator i.inst_opcode`
  >- (`u = jump_to u.vs_current_bb w` by metis_tac[scfg_terminator_jump] >>
      `~u.vs_halted` by
        (qpat_x_assum `u = jump_to _ w` (fn th => once_rewrite_tac[th]) >>
         simp[jump_to_def]) >>
      `bw.bb_label <> a.bb_label` by
        metis_tac[scfg_chain_segment_terminator_source, lookup_block_member_label] >>
      `exec_block k C bw w = OK u` by simp[Once exec_block_def] >>
      `r = OK u` by metis_tac[scfg_chain_source_stop] >>
      drule_all scfg_chain_segment_terminator_exit >> strip_tac >>
      `~v.vs_halted` by
        (qpat_x_assum `scfg_chain_exit a b u v` mp_tac >>
         simp[scfg_chain_exit_def, scfg_payload_def] >> strip_tac >>
         qpat_x_assum `v = scfg_ctrl _ _ _ u`
           (fn th => once_rewrite_tac[th]) >> simp[scfg_ctrl_def]) >>
      qexistsl_tac [`k`, `OK v`] >>
      simp[Once exec_block_def, scfg_result_def] >>
      fs[scfg_chain_exit_def]) >>
  drule_all scfg_chain_source_cancel >>
  disch_then assume_tac >>
  drule_all scfg_chain_segment_advance >>
  disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  `u.vs_halted = w.vs_halted` by
    (qpat_assum `step_inst k C i w = OK u`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_halted) >> simp[]) >>
  `u.vs_current_bb = w.vs_current_bb` by
    (qpat_assum `step_inst k C i w = OK u`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_control_flow) >> simp[]) >>
  `v.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `step_inst k C i t = OK v`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_control_flow) >> simp[]) >>
  `!j. active_inst fn j (u with vs_inst_idx := SUC w.vs_inst_idx) ==>
     frame_reach C fn s0 j (u with vs_inst_idx := SUC w.vs_inst_idx)` by
    metis_tac[frame_reach_rules] >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `LENGTH bt.bb_instructions - SUC t.vs_inst_idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`fn`, `a`, `b`, `C`, `s0`,
    `u with vs_inst_idx := SUC w.vs_inst_idx`,
    `v with vs_inst_idx := SUC t.vs_inst_idx`, `bw`, `bt`, `r`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `m` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `scfg_result r q` >>
  `terminates q` by metis_tac[scfg_result_terminates] >>
  `!e. q <> Error e` by (Cases_on `q` >> gvs[terminates_def]) >>
  `?m2. exec_block m2 C bt t = q` by
    (irule scfg_istep_continue >> simp[] >>
     qexistsl_tac [`k`, `m`, `v`] >> simp[Abbr `q`]) >>
  qexists_tac `m2` >> simp[]
QED

Finalise scfg_chain_exec_forward_distance

Theorem scfg_chain_exec_forward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((?k. exec_block k C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?k1 k2 x. bb.bb_label = a.bb_label /\
       exec_block k1 C bb s = OK x /\ ~x.vs_halted /\
       x.vs_current_bb = b.bb_label /\ run_block k2 C b x = r)) /\
  terminates r ==>
  ?m q. exec_block m C bt t = q /\ scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule scfg_chain_exec_forward_distance >> simp[] >> metis_tac[]
QED

(* Exact-budget source interfaces for forward chain contraction. *)
Theorem scfg_chain_source_splice_cancel_fuel:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_chain_splice a s t /\ ~s.vs_halted /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ((exec_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block N C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) ==>
  exec_block N C b (jump_to b.bb_label s) = r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bb = a` by (fs[scfg_chain_splice_def, scfg_chain_hyp_def] >> gvs[]) >>
  qpat_x_assum `bb = a` SUBST_ALL_TAC >>
  `exec_block N C a s = OK (jump_to b.bb_label s)` by
    (irule scfg_chain_splice_exec >> metis_tac[]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[] >>
  metis_tac[scfg_chain_run_right]
QED

Theorem scfg_chain_source_normalize_forward_fuel:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((exec_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block N C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) ==>
  ?w bw. scfg_chain_segment a b w t /\ ~w.vs_halted /\
    lookup_block w.vs_current_bb fn.fn_blocks = SOME bw /\
    (!i. active_inst fn i w ==> frame_reach C fn s0 i w) /\
    ((exec_block N C bw w = r /\
         (bw.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
     (?x. bw.bb_label = a.bb_label /\ exec_block N C bw w = OK x /\
         ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `scfg_chain_segment a b s t \/ _` strip_assume_tac
  >- (qexistsl_tac [`s`, `bb`] >> simp[]) >>
  drule_all scfg_chain_source_splice_cancel_fuel >> strip_tac >>
  drule_all scfg_chain_splice_rooted >> strip_tac >>
  qexistsl_tac [`jump_to b.bb_label s`, `b`] >>
  `a.bb_label <> b.bb_label` by metis_tac[scfg_chain_distinct_labels] >>
  `lookup_block b.bb_label fn.fn_blocks = SOME b` by fs[scfg_chain_hyp_def] >>
  simp[jump_to_def] >> metis_tac[jump_to_def]
QED

Theorem scfg_chain_source_head_fuel:
  ((exec_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block N C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) /\
  terminates r ==>
  ?i z. get_instruction bb s.vs_inst_idx = SOME i /\
    step_inst N C i s = z /\ terminates z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?z. exec_block N C bb s = z /\ terminates z` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     goal_assum (drule_at (Pos hd)) >> simp[terminates_def]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `terminates r` kall_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [exec_block_def]) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[]
  >- (strip_tac >> gvs[terminates_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `step_inst N C i s` >> simp[] >>
  rpt strip_tac >> gvs[terminates_def] >> metis_tac[]
QED

Theorem scfg_chain_source_cancel_fuel:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst N C i s = OK u /\
  ((exec_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block N C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) /\
  terminates r ==>
  (exec_block N C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = r /\
       (bb.bb_label <> a.bb_label \/ (!v. r <> OK v))) \/
  (?x. bb.bb_label = a.bb_label /\
       exec_block N C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r)
Proof
  strip_tac >>
  `exec_block N C bb s =
   exec_block N C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >> simp[]) >>
  metis_tac[]
QED

Theorem scfg_chain_exec_forward_fuel:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((exec_block N C bb s = r /\
       (bb.bb_label <> a.bb_label \/ (!u. r <> OK u))) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block N C bb s = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ run_block N C b x = r)) /\
  terminates r ==>
  ?q. exec_block N C bt t = q /\ scfg_result r q /\
    (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)
Proof
  qid_spec_tac `r` >> qid_spec_tac `bb` >> qid_spec_tac `s` >>
  qid_spec_tac `t` >>
  measureInduct_on `LENGTH bt.bb_instructions - t.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> rename1 `idx = t.vs_inst_idx` >>
  rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_source_normalize_forward_fuel >>
  disch_then (qx_choose_then `w` (qx_choose_then `bw`
    (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `scfg_chain_segment a b s t \/ _` kall_tac >>
  qpat_x_assum `lookup_block s.vs_current_bb _ = _` kall_tac >>
  qpat_x_assum `!i. active_inst fn i s ==> _` kall_tac >>
  qpat_x_assum `~s.vs_halted` kall_tac >>
  qpat_x_assum `(exec_block N C bb s = r /\ _) \/ _` kall_tac >>
  drule_all scfg_chain_source_head_fuel >> strip_tac >>
  `i.inst_opcode <> PHI` by metis_tac[scfg_step_terminates_nonphi] >>
  `active_inst fn i w` by
    (irule scfg_lookup_active >> qexistsl_tac [`w`, `bw`] >>
     metis_tac[lookup_block_member_label]) >>
  `frame_reach C fn s0 i w` by metis_tac[] >>
  `get_instruction bt t.vs_inst_idx = SOME i` by
    metis_tac[scfg_chain_segment_instruction, optionTheory.SOME_11] >>
  Cases_on `?u. z = OK u`
  >- (pop_assum (qx_choose_then `u` SUBST_ALL_TAC) >> suspend "ok") >>
  `!u. z <> OK u` by metis_tac[] >>
  `exec_block N C bw w = z` by metis_tac[scfg_exec_terminal] >>
  `r = z` by (irule scfg_chain_source_stop >> simp[] >> metis_tac[]) >>
  `scfg_payload w t` by metis_tac[scfg_chain_segment_payload] >>
  `scfg_result z (step_inst N C i t)` by metis_tac[scfg_payload_step] >>
  `!u. step_inst N C i t <> OK u` by
    (qpat_x_assum `scfg_result z _` mp_tac >>
     qpat_x_assum `!u. z <> OK u` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `z` >> Cases_on `step_inst N C i t` >> simp[scfg_result_def]) >>
  qexists_tac `step_inst N C i t` >> simp[] >>
  metis_tac[scfg_exec_terminal]
QED

Resume scfg_chain_exec_forward_fuel[ok]:
  Cases_on `is_terminator i.inst_opcode`
  >- (`u = jump_to u.vs_current_bb w` by metis_tac[scfg_terminator_jump] >>
      `~u.vs_halted` by
        (qpat_x_assum `u = jump_to _ w` (fn th => once_rewrite_tac[th]) >>
         simp[jump_to_def]) >>
      `bw.bb_label <> a.bb_label` by
        metis_tac[scfg_chain_segment_terminator_source, lookup_block_member_label] >>
      `exec_block N C bw w = OK u` by simp[Once exec_block_def] >>
      `r = OK u` by (irule scfg_chain_source_stop >> simp[] >> metis_tac[]) >>
      drule_all scfg_chain_segment_terminator_exit >> strip_tac >>
      `~v.vs_halted` by
        (qpat_x_assum `scfg_chain_exit a b u v` mp_tac >>
         simp[scfg_chain_exit_def, scfg_payload_def] >> strip_tac >>
         qpat_x_assum `v = scfg_ctrl _ _ _ u`
           (fn th => once_rewrite_tac[th]) >> simp[scfg_ctrl_def]) >>
      qexists_tac `OK v` >>
      simp[Once exec_block_def, scfg_result_def] >> fs[scfg_chain_exit_def]) >>
  drule_all scfg_chain_source_cancel_fuel >> disch_then assume_tac >>
  drule_all scfg_chain_segment_advance >>
  disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  `u.vs_halted = w.vs_halted` by
    (qpat_assum `step_inst N C i w = OK u`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_halted) >> simp[]) >>
  `u.vs_current_bb = w.vs_current_bb` by
    (qpat_assum `step_inst N C i w = OK u`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_control_flow) >> simp[]) >>
  `v.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `step_inst N C i t = OK v`
       (mp_then Any mp_tac venomInstPropsTheory.step_preserves_control_flow) >> simp[]) >>
  `!j. active_inst fn j (u with vs_inst_idx := SUC w.vs_inst_idx) ==>
     frame_reach C fn s0 j (u with vs_inst_idx := SUC w.vs_inst_idx)` by
    metis_tac[frame_reach_rules] >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `?q. exec_block N C bt (v with vs_inst_idx := SUC t.vs_inst_idx) = q /\
       scfg_result r q /\
       (!u v. r = OK u /\ q = OK v ==> scfg_chain_exit a b u v)` by
    (first_x_assum irule >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `q` >> simp[] >>
  CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >> simp[]
QED

Finalise scfg_chain_exec_forward_fuel
