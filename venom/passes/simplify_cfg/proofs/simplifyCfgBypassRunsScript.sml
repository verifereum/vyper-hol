(* Block-local runs and finite instruction prefixes for bypass. *)
Theory simplifyCfgBypassRuns
Ancestors
  simplifyCfgBypassExec simplifyCfgBypassEntry simplifyCfgFragments
  simplifyCfgControl simplifyCfgControlExec simplifyCfgBypassShape
  simplifyCfgBypassClosure venomInstProps venomExecProofs
  venomExecSemantics venomState venomInst list simplifyCfgFixupStatic venomWf
  o1PassLift contextCodegenRel simplifyCfgBypassPrecondition simplifyCfgDefs
  venomExecProps simplifyCfgMergeRuns cfgTransform simplifyCfgStaticInterface
  simplifyCfgSimTools simplifyCfgBypassStatic instIdxIndep simplifyCfgMergeSegment
  simplifyCfgAvailability

Theorem scfg_bypass_ordinary_advance:
  scfg_bypass_aligned a b s t /\ ~is_terminator i.inst_opcode /\
  step_inst k C i s = OK u ==>
  step_inst k C i t = OK
    (scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s.vs_inst_idx u) /\
  scfg_bypass_aligned a b (u with vs_inst_idx := SUC s.vs_inst_idx)
    ((scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s.vs_inst_idx u) with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> conj_tac
  >- (irule scfg_bypass_ordinary_step_OK >> simp[]) >>
  drule_all step_preserves_control_flow >> strip_tac >>
  fs[scfg_bypass_aligned_def, scfg_ctrl_def]
QED

Theorem scfg_bypass_iprefix_forward:
  !C bb s u. scfg_iprefix C bb s u ==>
  !a b t. bb_well_formed bb /\
    phi_prefix_length bb.bb_instructions <= s.vs_inst_idx /\
    scfg_bypass_aligned a b s t ==>
    ?v. scfg_iprefix C (scfg_bypass_block a b bb) t v /\
      scfg_bypass_aligned a b u v
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac
  >- metis_tac[scfg_iprefix_rules] >>
  `i.inst_opcode <> PHI` by
    (`EVERY (\i. i.inst_opcode <> PHI)
       (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
     fs[get_instruction_def, EVERY_EL] >>
     first_x_assum (qspec_then
       `s.vs_inst_idx - phi_prefix_length bb.bb_instructions` mp_tac) >>
     simp[LENGTH_DROP, EL_DROP]) >>
  drule_all scfg_bypass_ordinary_advance >> strip_tac >>
  first_x_assum (qspecl_then [`a`, `b`] mp_tac) >> simp[] >>
  disch_then drule >> strip_tac >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME i` by
    (fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
     irule scfg_bypass_instruction_ordinary >> simp[]) >>
  goal_assum (drule_at Any) >>
  metis_tac[scfg_iprefix_rules]
QED

Theorem scfg_bypass_instruction_ordinary_inv:
  get_instruction (scfg_bypass_block a b bb) n = SOME i /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  get_instruction bb n = SOME i
Proof
  strip_tac >> fs[scfg_bypass_instruction] >>
  Cases_on `get_instruction bb n` >> gvs[] >>
  simp[scfg_bypass_image_ordinary]
QED

Theorem scfg_bypass_ordinary_advance_back:
  ctx_bisim C C' /\ scfg_bypass_aligned a b s t /\
  ~is_terminator i.inst_opcode /\ step_inst k' C' i t = OK v ==>
  ?k u. step_inst k C i s = OK u /\
    scfg_bypass_aligned a b (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule_all scfg_bypass_ordinary_step_back >> strip_tac >>
  drule_all scfg_bypass_ordinary_advance >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem scfg_bypass_iprefix_backward:
  !C' mb t v. scfg_iprefix C' mb t v ==>
  !C bb a b s. ctx_bisim C C' /\ mb = scfg_bypass_block a b bb /\
    bb_well_formed mb /\ phi_prefix_length mb.bb_instructions <= t.vs_inst_idx /\
    scfg_bypass_aligned a b s t ==>
    ?u. scfg_iprefix C bb s u /\ scfg_bypass_aligned a b u v
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac
  >- metis_tac[scfg_iprefix_rules] >>
  `i.inst_opcode <> PHI` by
    (`EVERY (\i. i.inst_opcode <> PHI)
       (DROP (phi_prefix_length mb.bb_instructions) mb.bb_instructions)` by
       (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
     qpat_x_assum `mb = _` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `EVERY _ (DROP _ _)` mp_tac >>
     rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then
       `t.vs_inst_idx - phi_prefix_length mb.bb_instructions` mp_tac) >>
     fs[get_instruction_def, LENGTH_DROP, EL_DROP]) >>
  drule_all scfg_bypass_ordinary_advance_back >> strip_tac >>
  first_x_assum (drule_at (Pos last)) >> simp[] >>
  disch_then (qspecl_then [`C`, `bb`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (`s.vs_inst_idx = t.vs_inst_idx` by
       fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
     irule scfg_bypass_instruction_ordinary_inv >> metis_tac[]) >>
  goal_assum (drule_at Any) >> metis_tac[scfg_iprefix_rules]
QED

Theorem scfg_bypass_iprefix_observe:
  ctx_bisim C C' /\ scfg_iprefix C' (scfg_bypass_block a b bb) t v /\
  bb_well_formed (scfg_bypass_block a b bb) /\
  phi_prefix_length (scfg_bypass_block a b bb).bb_instructions <= t.vs_inst_idx /\
  scfg_bypass_aligned a b s t /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  get_instruction (scfg_bypass_block a b bb) v.vs_inst_idx = SOME j ==>
  ?u i. scfg_iprefix C bb s u /\ frame_reach C fn s0 i u /\
    get_instruction bb u.vs_inst_idx = SOME i /\
    j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i /\
    scfg_bypass_aligned a b u v
Proof
  strip_tac >>
  `?u. scfg_iprefix C bb s u /\ scfg_bypass_aligned a b u v` by
    (irule scfg_bypass_iprefix_backward >> metis_tac[]) >>
  `u.vs_inst_idx = v.vs_inst_idx` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `?i. get_instruction bb u.vs_inst_idx = SOME i /\
       j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i` by
    (fs[scfg_bypass_instruction] >>
     Cases_on `get_instruction bb v.vs_inst_idx` >> gvs[]) >>
  qexistsl_tac [`u`, `i`] >> simp[] >>
  irule scfg_iprefix_frame_reach >> metis_tac[]
QED

Theorem scfg_bypass_singleton_enters:
  scfg_bypass_hyp fn a b fn' ==>
  enters_block fn (jump_to b.bb_label s) (jump_to b.bb_label s) /\
  active_inst fn (LAST b.bb_instructions) (jump_to b.bb_label s)
Proof
  strip_tac >> drule scfg_bypass_singleton_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    (qpat_assum `b.bb_instructions = [_]` (fn th => once_rewrite_tac[th]) >>
     gvs[]) >>
  `phi_prefix_length b.bb_instructions = 0` by
    metis_tac[no_phis_phi_prefix_length_zero] >>
  `lookup_block b.bb_label fn.fn_blocks = SOME b` by fs[scfg_bypass_hyp_def] >>
  (conj_tac
   >- (simp[enters_block_def, jump_to_def, eval_phis_no_phis]) >>
   simp[active_inst_def, jump_to_def] >>
   qexists_tac `b` >> simp[get_instruction_def] >>
   drule lookup_block_member_label >> strip_tac >>
   qpat_assum `b.bb_instructions = [_]` (fn th => once_rewrite_tac[th]) >> simp[])
QED

Theorem scfg_bypass_singleton_reach:
  scfg_bypass_hyp fn a b fn' /\ frame_reach C fn s0 i s /\
  is_terminator i.inst_opcode /\ step_inst k C i s = OK (jump_to b.bb_label s) /\
  ~s.vs_halted ==>
  frame_reach C fn s0 (LAST b.bb_instructions) (jump_to b.bb_label s)
Proof
  strip_tac >> drule scfg_bypass_singleton_enters >> strip_tac >>
  irule (cj 3 frame_reach_rules) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`k`, `i`, `s`, `jump_to b.bb_label s`] >>
  simp[jump_to_def]
QED

Theorem scfg_bypass_singleton_prefix:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST b.bb_instructions) (jump_to b.bb_label s) /\
  ~s.vs_halted ==>
  scfg_bprefix C fn (jump_to b.bb_label s)
    (jump_to (HD (bb_succs b)) (jump_to b.bb_label s))
Proof
  strip_tac >> irule scfg_bprefix_single >>
  conj_tac >- simp[jump_to_def] >> qexistsl_tac [`b`, `0`] >>
  `lookup_block b.bb_label fn.fn_blocks = SOME b` by fs[scfg_bypass_hyp_def] >>
  `(jump_to b.bb_label s).vs_inst_idx = 0` by simp[jump_to_def] >>
  drule_all scfg_bypass_singleton_run >>
  simp[jump_to_def]
QED

Theorem scfg_bypass_source_successor_rooted:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST a.bb_instructions) s /\
  s.vs_current_bb = a.bb_label /\ ~s.vs_halted ==>
  ?l t. step_inst k C (LAST a.bb_instructions) s = OK (jump_to l s) /\
    step_inst k' C' (scfg_bypass_term b.bb_label (HD (bb_succs b))
      (LAST a.bb_instructions)) (scfg_ctrl a.bb_label prev n s) = OK t /\
    scfg_bypass_aligned a b
      (if l = b.bb_label then jump_to (HD (bb_succs b)) (jump_to l s)
       else jump_to l s) t /\
    scfg_bprefix C fn (jump_to l s)
      (if l = b.bb_label then jump_to (HD (bb_succs b)) (jump_to l s)
       else jump_to l s)
Proof
  strip_tac >> drule_all scfg_bypass_source_successor >>
  disch_then (qspec_then `prev` mp_tac) >>
  disch_then (qspec_then `n` mp_tac) >>
  disch_then (qspec_then `k'` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  qexistsl_tac [`l`, `t`] >> simp[] >>
  Cases_on `l = b.bb_label`
  >- (gvs[] >>
      `is_terminator (LAST a.bb_instructions).inst_opcode` by
        (drule scfg_bypass_source_shape >> strip_tac >> simp[is_terminator_def]) >>
      `frame_reach C fn s0 (LAST b.bb_instructions) (jump_to b.bb_label s)` by
        metis_tac[scfg_bypass_singleton_reach] >>
      metis_tac[scfg_bypass_singleton_prefix]) >>
  simp[scfg_bprefix_rules]
QED

Theorem scfg_bypass_nonsource_successor:
  scfg_bypass_hyp fn a b fn' /\ active_inst fn i s /\
  is_terminator i.inst_opcode /\ s.vs_current_bb <> a.bb_label /\
  step_inst k C i s = OK u /\ ~u.vs_halted ==>
  u.vs_current_bb <> b.bb_label
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, scfg_static_inst_wf] >>
  `inst_wf i` by metis_tac[active_inst_wf] >>
  `i.inst_opcode <> INVOKE` by (Cases_on `i.inst_opcode` >> fs[is_terminator_def]) >>
  `step_inst_base i s = OK u` by fs[Once step_inst_def] >>
  `MEM u.vs_current_bb (get_successors i)` by
    metis_tac[step_inst_base_term_succs] >>
  drule_all scfg_active_terminator_last >> strip_tac >>
  `MEM u.vs_current_bb (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def, MEM_nub]) >>
  `block_preds fn b.bb_label = [a]` by
    (irule scfg_bypass_preds >> fs[scfg_bypass_hyp_def]) >>
  strip_tac >>
  `MEM bb (block_preds fn b.bb_label)` by
    (rewrite_tac[block_preds_def, MEM_FILTER] >> metis_tac[]) >>
  gvs[]
QED

Theorem scfg_bypass_nonsource_branch:
  scfg_bypass_hyp fn a b fn' /\ active_inst fn i s /\
  is_terminator i.inst_opcode /\ s.vs_current_bb <> a.bb_label /\
  scfg_bypass_aligned a b s t /\ step_inst k C i s = OK u /\ ~u.vs_halted ==>
  ?v. step_inst k C
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t = OK v /\
    scfg_bypass_aligned a b u v
Proof
  strip_tac >>
  `u.vs_current_bb <> b.bb_label` by metis_tac[scfg_bypass_nonsource_successor] >>
  drule_all scfg_terminator_jump >> strip_tac >>
  `u.vs_prev_bb = SOME s.vs_current_bb /\ u.vs_inst_idx = 0` by
    (qpat_x_assum `u = jump_to _ _` mp_tac >>
     simp[jump_to_def, venom_state_component_equality]) >>
  `i.inst_opcode <> PHI` by (Cases_on `i.inst_opcode` >> fs[is_terminator_def]) >>
  `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i = i` by
    simp[scfg_bypass_image_def, update_phi_bypass_def] >>
  fs[scfg_bypass_aligned_def] >>
  `MEM i.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  simp[scfg_ctrl_branch, exec_result_map_def] >>
  gvs[jump_to_def, scfg_ctrl_def]
QED

Theorem scfg_bypass_terminator_successor:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  scfg_bypass_aligned a b s t /\ step_inst k C i s = OK u /\ ~u.vs_halted ==>
  ?v w. step_inst k C
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t = OK v /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  Cases_on `s.vs_current_bb = a.bb_label`
  >- suspend "source" >>
  drule_all scfg_bypass_nonsource_branch >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[scfg_bprefix_rules]
QED

Resume scfg_bypass_terminator_successor[source]:
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  drule_all scfg_active_terminator_last >> strip_tac >>
  `MEM a fn.fn_blocks` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[lookup_block_member_label]) >>
  `bb = a` by metis_tac[same_label_same_block] >> gvs[] >>
  `~s.vs_halted` by
    (drule_all scfg_terminator_jump >> simp[jump_to_def, venom_state_component_equality]) >>
  drule_all scfg_bypass_source_successor_rooted >>
  disch_then (qspec_then
    `OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb` mp_tac) >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `k` mp_tac) >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `u = jump_to l s` by gvs[] >> gvs[] >>
  `is_terminator (scfg_bypass_term b.bb_label (HD (bb_succs b))
     (LAST a.bb_instructions)).inst_opcode` by
    metis_tac[scfg_bypass_term_opcode, is_terminator_def] >>
  fs[scfg_bypass_aligned_def] >>
  qexists_tac `if l = b.bb_label then
    jump_to (HD (bb_succs b)) (jump_to l s) else jump_to l s` >>
  simp[scfg_bypass_image_def, update_phi_bypass_def] >>
  rpt IF_CASES_TAC >> gvs[is_terminator_def]
QED
Finalise scfg_bypass_terminator_successor

Theorem scfg_bypass_exec_OK_forward:
  !s. !C fn a b fn' s0 bb t k u.
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  scfg_bypass_aligned a b s t /\ exec_block k C bb s = OK u /\ ~u.vs_halted ==>
  ?v w. exec_block k C (scfg_bypass_block a b bb) t = OK v /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
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
  simp[] >> strip_tac >>
  suspend "ordinary"
QED

Resume scfg_bypass_exec_OK_forward[transfer]:
  qpat_x_assum `!y. LENGTH _ - _ < _ ==> _` kall_tac >>
  Cases_on `next.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
  `frame_reach C fn s0 i s` by metis_tac[] >>
  drule_all scfg_bypass_terminator_successor >> strip_tac >>
  qexistsl_tac [`v`, `w`] >> simp[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME
     (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i)` by
    (simp[scfg_bypass_instruction] >> metis_tac[]) >>
  `is_terminator (scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) bb.bb_label i).inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  `~w.vs_halted` by (drule scfg_bprefix_last >> metis_tac[]) >>
  `~v.vs_halted` by
    (qpat_x_assum `scfg_bypass_aligned a b w v` mp_tac >>
     simp[scfg_bypass_aligned_def, scfg_ctrl_def] >> rpt strip_tac >> gvs[]) >>
  simp[Once exec_block_def]
QED

Resume scfg_bypass_exec_OK_forward[ordinary]:
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
  disch_then (qx_choosel_then [`v2`, `w`] strip_assume_tac) >>
  qexistsl_tac [`v2`, `w`] >> simp[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  `get_instruction (scfg_bypass_block a b bb) t.vs_inst_idx = SOME i` by
    (irule scfg_bypass_instruction_ordinary >> metis_tac[]) >>
  simp[Once exec_block_def] >> metis_tac[]
QED
Finalise scfg_bypass_exec_OK_forward

Theorem scfg_bypass_run_block_OK_forward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k C bb s = OK u /\ ~u.vs_halted ==>
  ?v w. run_block k C (scfg_bypass_block a b bb) t = OK v /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
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
  irule scfg_bypass_exec_OK_forward >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`r with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `s0`] >> simp[]) >>
  metis_tac[]
QED

Theorem scfg_bypass_terminator_back:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  scfg_bypass_aligned a b s t /\
  step_inst k C
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t = OK v /\
  ~v.vs_halted ==>
  ?u w. step_inst k C i s = OK u /\ ~u.vs_halted /\ scfg_bprefix C fn u w /\
    scfg_bypass_aligned a b w v
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[frame_reach_active] >>
  Cases_on `s.vs_current_bb = a.bb_label`
  >- suspend "source" >>
  `i.inst_opcode <> PHI` by (Cases_on `i.inst_opcode` >> fs[is_terminator_def]) >>
  `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i = i` by
    simp[scfg_bypass_image_def, update_phi_bypass_def] >>
  `MEM i.inst_opcode [JMP; JNZ; DJMP]` by metis_tac[scfg_terminator_jump] >>
  `?u. step_inst k C i s = OK u` by
    (qpat_x_assum `step_inst _ _ _ t = OK _` mp_tac >>
     fs[scfg_bypass_aligned_def] >> simp[scfg_ctrl_branch] >>
     Cases_on `step_inst k C i s` >> simp[exec_result_map_def]) >>
  `~u.vs_halted` by
    (qpat_x_assum `step_inst _ _ _ t = OK _` mp_tac >>
     fs[scfg_bypass_aligned_def] >>
     simp[scfg_ctrl_branch, exec_result_map_def, scfg_ctrl_def] >>
     strip_tac >> gvs[]) >>
  drule_all scfg_bypass_terminator_successor >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> gvs[]
QED

Resume scfg_bypass_terminator_back[source]:
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
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
  `(LAST a.bb_instructions).inst_opcode <> PHI` by
    (Cases_on `(LAST a.bb_instructions).inst_opcode` >> fs[is_terminator_def]) >>
  `v = jump_to (if l = b.bb_label then HD (bb_succs b) else l) t` by
    (fs[scfg_bypass_image_def, update_phi_bypass_def, scfg_bypass_aligned_def] >>
     rpt IF_CASES_TAC >> gvs[is_terminator_def]) >>
  `~s.vs_halted` by
    (gvs[scfg_bypass_aligned_def, jump_to_def, scfg_ctrl_def]) >>
  `~(jump_to l s).vs_halted` by simp[jump_to_def] >>
  drule_all scfg_bypass_terminator_successor >> strip_tac >>
  qexistsl_tac [`jump_to l s`, `w`] >> gvs[]
QED
Finalise scfg_bypass_terminator_back

Theorem scfg_bypass_exec_OK_backward:
  !t. !C fn a b fn' s0 bb s k v.
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  scfg_bypass_aligned a b s t /\
  exec_block k C (scfg_bypass_block a b bb) t = OK v /\ ~v.vs_halted ==>
  ?u w. exec_block k C bb s = OK u /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
Proof
  rpt gen_tac >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - t.vs_inst_idx` >>
  rpt strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, scfg_bypass_instruction] >>
  Cases_on `get_instruction bb t.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb t.vs_inst_idx = SOME i` >>
  Cases_on `step_inst k C
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK next` >>
  `is_terminator (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i).inst_opcode =
    is_terminator i.inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  Cases_on `is_terminator i.inst_opcode`
  >- suspend "transfer" >>
  simp[] >> strip_tac >> suspend "ordinary"
QED

Resume scfg_bypass_exec_OK_backward[transfer]:
  qpat_x_assum `!y. LENGTH _ - _ < _ ==> _` kall_tac >>
  Cases_on `next.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
  `frame_reach C fn s0 i s` by metis_tac[] >>
  drule_all scfg_bypass_terminator_back >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> simp[Once exec_block_def] >> metis_tac[]
QED

Resume scfg_bypass_exec_OK_backward[ordinary]:
  `i.inst_opcode <> PHI` by
    metis_tac[scfg_step_OK_nonphi, scfg_bypass_image_opcode, is_terminator_def] >>
  `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i = i` by
    simp[scfg_bypass_image_ordinary] >>
  `step_inst k C i t = OK next` by gvs[] >>
  `?old. step_inst k C i s = OK old` by
    (`scfg_result (step_inst k C i s) (OK next)` by
       metis_tac[scfg_bypass_ordinary_result] >>
     Cases_on `step_inst k C i s` >> gvs[scfg_result_def]) >>
  drule_all scfg_bypass_ordinary_advance >> strip_tac >>
  `scfg_bypass_aligned a b (old with vs_inst_idx := SUC s.vs_inst_idx)
    (next with vs_inst_idx := SUC t.vs_inst_idx)` by gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[get_instruction_def, AllCaseEqs()] >>
  `old.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `!j. get_instruction bb (SUC s.vs_inst_idx) = SOME j ==>
    frame_reach C fn s0 j (old with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >> irule (cj 2 frame_reach_rules) >> conj_tac
     >- (simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
     qexistsl_tac [`k`, `i`] >> simp[]) >>
  first_x_assum (qspec_then `SUC t.vs_inst_idx` mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qspec_then `next with vs_inst_idx := SUC t.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspec_then `old with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> simp[Once exec_block_def] >> metis_tac[]
QED
Finalise scfg_bypass_exec_OK_backward

Theorem scfg_bypass_run_block_OK_backward:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k C (scfg_bypass_block a b bb) t = OK v /\ ~v.vs_halted ==>
  ?u w. run_block k C bb s = OK u /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf, scfg_static_inst_wf] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `(case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb)` by
    (drule_all scfg_bprefix_incoming >> strip_tac >> gvs[fn_entry_state_def]) >>
  `?r. eval_phis t (scfg_bypass_block a b bb).bb_instructions = OK r /\
    exec_block k C (scfg_bypass_block a b bb)
      (r with vs_inst_idx := phi_prefix_length (scfg_bypass_block a b bb).bb_instructions) = OK v` by
    (qspecl_then [`t`, `(scfg_bypass_block a b bb).bb_instructions`]
       strip_assume_tac eval_phis_ok_or_error_defs >>
     qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
     simp[run_block_def] >> metis_tac[]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >> disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  `enters_block fn' t
    (r with vs_inst_idx := phi_prefix_length (scfg_bypass_block a b bb).bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  drule_all scfg_bypass_enters_block >> disch_then (drule o iffLR) >> strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb` by
    (fs[enters_block_def] >> metis_tac[eval_phis_preserves_current_bb]) >>
  `!i. get_instruction bb s1.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s1` by
    (rpt strip_tac >> irule scfg_bprefix_enter_reach >> reverse conj_tac
     >- (qexists_tac `s` >> simp[]) >>
     simp[active_inst_def] >> qexists_tac `bb` >> gvs[get_instruction_def]) >>
  `?u w. exec_block k C bb s1 = OK u /\ scfg_bprefix C fn u w /\
    scfg_bypass_aligned a b w v` by
    (irule scfg_bypass_exec_OK_backward >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  qpat_x_assum `enters_block fn s s1` mp_tac >> simp[enters_block_def] >> strip_tac >>
  gvs[run_block_def]
QED
