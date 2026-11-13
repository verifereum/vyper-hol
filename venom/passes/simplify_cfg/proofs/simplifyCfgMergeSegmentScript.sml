(* Control-coordinate positions in a contracted two-block chain. *)
Theory simplifyCfgMergeSegment
Ancestors
  simplifyCfgMergeEntry simplifyCfgFragments simplifyCfgControl simplifyCfgControlExec
  simplifyCfgMergeExec simplifyCfgMergePaths simplifyCfgDefs venomExecProofs venomInstProofs
  contextCodegenRel o1PassLift passSimulationDefs venomExecSemantics venomInst
  venomState venomWf cfgTransform cfgHelpers list rich_list
  simplifyCfgStaticInterface unitLabelMapIdentity instIdxIndep simplifyCfgSimTools

Definition scfg_chain_segment_def:
  scfg_chain_segment a b s t <=>
    scfg_payload s t /\
    ((s.vs_current_bb = a.bb_label /\ t.vs_current_bb = a.bb_label /\
      s.vs_inst_idx = t.vs_inst_idx /\
      s.vs_inst_idx < LENGTH (FRONT a.bb_instructions)) \/
     (s.vs_current_bb = b.bb_label /\ t.vs_current_bb = a.bb_label /\
      t.vs_inst_idx = LENGTH (FRONT a.bb_instructions) + s.vs_inst_idx) \/
     (s.vs_current_bb <> a.bb_label /\ s.vs_current_bb <> b.bb_label /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx))
End

Definition scfg_chain_exit_def:
  scfg_chain_exit a b s t <=>
    scfg_payload s t /\ s.vs_current_bb = t.vs_current_bb /\
    s.vs_current_bb <> b.bb_label /\ s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    t.vs_prev_bb = OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb
End

Theorem scfg_chain_segment_payload:
  scfg_chain_segment a b s t ==> scfg_payload s t
Proof
  simp[scfg_chain_segment_def]
QED

Theorem scfg_chain_segment_observation:
  inst_wf i /\ scfg_chain_segment a b s t ==> mem_corr i s i t /\ call_corr i s i t
Proof
  strip_tac >> drule scfg_chain_segment_payload >> strip_tac >>
  metis_tac[scfg_payload_mem_corr, scfg_payload_call_corr]
QED

Theorem scfg_chain_instruction_other:
  bb.bb_label <> a.bb_label /\ get_instruction bb n = SOME i /\ i.inst_opcode <> PHI ==>
  get_instruction (scfg_chain_block a b bb) n = SOME i
Proof
  simp[scfg_chain_block_def, get_instruction_def] >> strip_tac >>
  gvs[EL_MAP] >> simp[scfg_phi_image_nonphi]
QED

Theorem scfg_chain_segment_instruction:
  scfg_chain_hyp fn a b /\ scfg_chain_segment a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI ==>
  ?bt. lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME i
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  fs[scfg_chain_segment_def]
  >- (`bb = a` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
      qexists_tac `scfg_chain_block a b a` >>
      conj_tac >- metis_tac[scfg_chain_lookup_member, scfg_chain_distinct_labels] >>
      irule EQ_TRANS >>
      qexists_tac `SOME (EL t.vs_inst_idx a.bb_instructions)` >>
      conj_tac >- (irule scfg_chain_instruction_left_nonphi >> fs[get_instruction_def]) >>
      fs[get_instruction_def])
  >- (`bb = b` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
      qexists_tac `scfg_chain_block a b a` >>
      conj_tac >- metis_tac[scfg_chain_lookup_member, scfg_chain_hyp_def,
        lookup_block_member_label, scfg_chain_distinct_labels] >>
      drule scfg_chain_instruction_right_nonphi >>
      disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
      fs[get_instruction_def]) >>
  qexists_tac `scfg_chain_block a b bb` >>
  conj_tac >- metis_tac[scfg_chain_lookup_member] >>
  irule scfg_chain_instruction_other >> simp[]
QED

(* The left segment excludes the removed transfer itself. Its endpoint is
   a stuttering boundary, even when entry PHIs already end at d. *)
Definition scfg_chain_splice_def:
  scfg_chain_splice a s t <=>
    scfg_payload s t /\ s.vs_current_bb = a.bb_label /\
    t.vs_current_bb = a.bb_label /\
    s.vs_inst_idx = LENGTH (FRONT a.bb_instructions) /\
    t.vs_inst_idx = LENGTH (FRONT a.bb_instructions)
End

Theorem scfg_chain_segment_advance:
  scfg_chain_segment a b s t /\ ~is_terminator i.inst_opcode /\
  step_inst k C i s = OK u ==>
  ?v. step_inst k C i t = OK v /\
    (scfg_chain_segment a b (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx) \/
     scfg_chain_splice a (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >>
  `scfg_payload s t` by metis_tac[scfg_chain_segment_payload] >>
  `~MEM i.inst_opcode [JMP; JNZ; DJMP]` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `t = scfg_ctrl t.vs_current_bb t.vs_prev_bb t.vs_inst_idx s` by
    fs[scfg_payload_def] >>
  `step_inst k C i t =
    OK (scfg_ctrl t.vs_current_bb t.vs_prev_bb t.vs_inst_idx u)` by
    metis_tac[scfg_ctrl_step_OK] >>
  qexists_tac `scfg_ctrl t.vs_current_bb t.vs_prev_bb t.vs_inst_idx u` >>
  simp[] >>
  qpat_assum `step_inst k C i s = OK u`
    (mp_then Any mp_tac step_preserves_control_flow) >> simp[] >> strip_tac >>
  gvs[scfg_chain_segment_def] >>
  simp[scfg_chain_segment_def, scfg_chain_splice_def, scfg_payload_def, scfg_ctrl_def] >>
  `SUC t.vs_inst_idx < LENGTH (FRONT a.bb_instructions) \/
   SUC t.vs_inst_idx = LENGTH (FRONT a.bb_instructions)` by
    (qpat_x_assum `t.vs_inst_idx < _` mp_tac >> decide_tac) >> simp[]
QED

Theorem scfg_chain_splice_segment:
  scfg_chain_splice a s t ==>
  scfg_chain_segment a b (jump_to b.bb_label s) t
Proof
  simp[scfg_chain_splice_def, scfg_chain_segment_def,
    scfg_payload_def, scfg_ctrl_def, jump_to_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem scfg_chain_splice_transfer:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST a.bb_instructions) s /\
  scfg_chain_splice a s t ==>
  step_inst k C (LAST a.bb_instructions) s = OK (jump_to b.bb_label s) /\
  enters_block fn (jump_to b.bb_label s) (jump_to b.bb_label s) /\
  scfg_chain_segment a b (jump_to b.bb_label s) t
Proof
  strip_tac >> conj_tac >- metis_tac[scfg_chain_transfer_step] >>
  reverse conj_tac >- metis_tac[scfg_chain_splice_segment] >>
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    metis_tac[scfg_chain_no_phis, no_phis_def] >>
  simp[enters_block_def, jump_to_def] >>
  qexists_tac `b` >> simp[venomExecProofsTheory.eval_phis_no_phis,
    venomExecProofsTheory.no_phis_phi_prefix_length_zero] >>
  fs[scfg_chain_hyp_def]
QED

Theorem scfg_chain_phi_prefix_bound:
  scfg_chain_hyp fn a b ==>
  phi_prefix_length a.bb_instructions <= LENGTH (FRONT a.bb_instructions)
Proof
  strip_tac >>
  `a.bb_instructions <> []` by metis_tac[scfg_chain_blocks_nonempty] >>
  `(LAST a.bb_instructions).inst_opcode <> PHI` by
    (drule scfg_chain_transfer_shape >> strip_tac >> simp[]) >>
  qspec_then `a.bb_instructions` mp_tac
    (Q.INST [`ys` |-> `[]`] scfg_phi_splice) >> simp[] >>
  strip_tac >> metis_tac[phi_prefix_length_le]
QED

Theorem scfg_chain_enters_segment:
  scfg_chain_hyp fn a b /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_current_bb <> b.bb_label /\
  (case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb) /\
  enters_block fn s s1 ==>
  ?t1. enters_block (scfg_chain fn a b)
    (scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 s) t1 /\
    (scfg_chain_segment a b s1 t1 \/ scfg_chain_splice a s1 t1)
Proof
  strip_tac >> drule_all scfg_chain_enters_block >> strip_tac >>
  qexists_tac `scfg_ctrl s.vs_current_bb
    (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
    s1.vs_inst_idx s1` >>
  conj_tac >- metis_tac[] >>
  `s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = phi_prefix_length bb.bb_instructions` by
    (qpat_x_assum `enters_block fn s s1` mp_tac >>
     simp[enters_block_def] >> strip_tac >> gvs[] >>
     drule eval_phis_preserves_current_bb >> simp[]) >>
  Cases_on `s.vs_current_bb = a.bb_label`
  >- (`bb = a` by (fs[scfg_chain_hyp_def] >> gvs[]) >>
      drule scfg_chain_phi_prefix_bound >> strip_tac >>
      `phi_prefix_length a.bb_instructions < LENGTH (FRONT a.bb_instructions) \/
       phi_prefix_length a.bb_instructions = LENGTH (FRONT a.bb_instructions)` by
        (qpat_x_assum `phi_prefix_length _ <= _` mp_tac >> decide_tac) >>
      simp[scfg_chain_segment_def, scfg_chain_splice_def, scfg_ctrl_def,
        scfg_payload_def]) >>
  simp[scfg_chain_segment_def, scfg_chain_splice_def, scfg_ctrl_def,
    scfg_payload_def]
QED

Theorem scfg_result_terminal:
  scfg_result r r' /\ terminates r /\ (!s. r <> OK s) ==>
  frame_result_rel r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[scfg_result_def, terminates_def, frame_result_rel_def] >>
  strip_tac >> drule scfg_payload_frame >> simp[]
QED

Theorem scfg_chain_segment_terminal:
  scfg_chain_segment a b s t /\ terminates (step_inst k C i s) /\
  (!u. step_inst k C i s <> OK u) ==>
  frame_result_rel (step_inst k C i s) (step_inst k C i t)
Proof
  strip_tac >> irule scfg_result_terminal >> simp[] >>
  irule scfg_payload_step >> metis_tac[scfg_chain_segment_payload]
QED

Theorem scfg_chain_instruction_other_inverse:
  bb.bb_label <> a.bb_label /\
  get_instruction (scfg_chain_block a b bb) n = SOME i /\ i.inst_opcode <> PHI ==>
  get_instruction bb n = SOME i
Proof
  simp[scfg_chain_block_def, get_instruction_def, EL_MAP] >> strip_tac >>
  `scfg_phi_image a b bb.bb_label (EL n bb.bb_instructions) =
    EL n bb.bb_instructions` by
    (irule scfg_phi_image_nonphi >> metis_tac[scfg_phi_image_opcode]) >>
  gvs[]
QED

Theorem scfg_chain_segment_instruction_inverse:
  scfg_chain_hyp fn a b /\ scfg_chain_segment a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  get_instruction bt t.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI ==>
  get_instruction bb s.vs_inst_idx = SOME i
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  fs[scfg_chain_segment_def]
  >- (`bb = a` by
        (fs[scfg_chain_hyp_def] >>
         qpat_x_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` mp_tac >>
         simp[]) >> gvs[] >>
      `bt = scfg_chain_block a b a` by
        (drule scfg_chain_lookup_eq >> disch_then (qspec_then `a.bb_label` mp_tac) >>
         simp[scfg_chain_distinct_labels] >> metis_tac[optionTheory.SOME_11]) >>
      gvs[] >>
      `i = scfg_phi_image a b a.bb_label (EL t.vs_inst_idx a.bb_instructions)` by
        (qpat_x_assum `get_instruction _ _ = SOME i` mp_tac >>
         simp[scfg_chain_instruction_left]) >>
      gvs[] >>
      `scfg_phi_image a b a.bb_label (EL t.vs_inst_idx a.bb_instructions) =
        EL t.vs_inst_idx a.bb_instructions` by
        (irule scfg_phi_image_nonphi >> metis_tac[scfg_phi_image_opcode]) >>
      fs[get_instruction_def, scfg_chain_block_def] >>
      Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT])
  >- (`bb = b` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
      `bt = scfg_chain_block a b a` by
        (drule scfg_chain_lookup_eq >> disch_then (qspec_then `a.bb_label` mp_tac) >>
         fs[scfg_chain_hyp_def] >>
         simp[scfg_chain_distinct_labels] >> metis_tac[optionTheory.SOME_11]) >>
      gvs[] >>
      `s.vs_inst_idx < LENGTH b.bb_instructions` by
        fs[get_instruction_def, scfg_chain_block_def] >>
      drule_all scfg_chain_instruction_right_nonphi >>
      fs[get_instruction_def]) >>
  `bt = scfg_chain_block a b bb` by
    (drule scfg_chain_lookup_eq >> disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     simp[] >> metis_tac[optionTheory.SOME_11]) >>
  gvs[] >> irule scfg_chain_instruction_other_inverse >> metis_tac[]
QED

Theorem scfg_chain_splice_active:
  scfg_chain_hyp fn a b /\ scfg_chain_splice a s t ==>
  active_inst fn (LAST a.bb_instructions) s
Proof
  strip_tac >>
  `a.bb_instructions <> [] /\ MEM a fn.fn_blocks` by
    metis_tac[scfg_chain_blocks_nonempty, scfg_chain_hyp_def, lookup_block_member_label] >>
  simp[active_inst_def] >> qexists_tac `a` >>
  fs[scfg_chain_splice_def] >>
  Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT, LAST_EL]
QED

Theorem scfg_chain_splice_rooted:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_chain_splice a s t /\ ~s.vs_halted /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  scfg_chain_segment a b (jump_to b.bb_label s) t /\
  (!i. active_inst fn i (jump_to b.bb_label s) ==>
    frame_reach C fn s0 i (jump_to b.bb_label s))
Proof
  strip_tac >>
  `frame_reach C fn s0 (LAST a.bb_instructions) s` by
    metis_tac[scfg_chain_splice_active] >>
  drule_all scfg_chain_splice_transfer >> strip_tac >> simp[] >>
  rpt strip_tac >> irule (cj 3 frame_reach_rules) >>
  simp[] >> qexistsl_tac [`0`, `LAST a.bb_instructions`, `s`, `jump_to b.bb_label s`] >>
  simp[jump_to_def] >>
  drule scfg_chain_transfer_shape >> strip_tac >> simp[is_terminator_def]
QED

Theorem scfg_chain_segment_advance_back:
  scfg_chain_segment a b s t /\ ~is_terminator i.inst_opcode /\
  step_inst k C i t = OK v ==>
  ?u. step_inst k C i s = OK u /\
    (scfg_chain_segment a b (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx) \/
     scfg_chain_splice a (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >>
  `scfg_payload t s` by metis_tac[scfg_chain_segment_payload, scfg_payload_sym] >>
  drule scfg_payload_step >> disch_then (qspecl_then [`k`, `i`, `C`] mp_tac) >>
  simp[] >> Cases_on `step_inst k C i s` >> simp[scfg_result_def] >>
  strip_tac >> drule_all scfg_chain_segment_advance >> metis_tac[exec_result_11]
QED

(* Reachability is carried for whichever instruction is observed next; this
   also supplies the removed transfer when a finite prefix crosses the splice. *)
Theorem scfg_chain_segment_normalize:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  ?s' bb'. scfg_chain_segment a b s' t /\ ~s'.vs_halted /\
    lookup_block s'.vs_current_bb fn.fn_blocks = SOME bb' /\
    (!i. active_inst fn i s' ==> frame_reach C fn s0 i s')
Proof
  strip_tac
  >- (qexistsl_tac [`s`, `bb`] >> simp[]) >>
  drule_all scfg_chain_splice_rooted >> strip_tac >>
  qexistsl_tac [`jump_to b.bb_label s`, `b`] >>
  fs[scfg_chain_hyp_def, jump_to_def]
QED

Theorem scfg_chain_segment_rooted_advance:
  scfg_chain_segment a b s t /\ ~is_terminator i.inst_opcode /\
  step_inst k C i t = OK v /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (!j. active_inst fn j s ==> frame_reach C fn s0 j s) ==>
  ?u. step_inst k C i s = OK u /\
    (scfg_chain_segment a b (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx) \/
     scfg_chain_splice a (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC t.vs_inst_idx)) /\
    ~u.vs_halted /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    (!j. active_inst fn j (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
      frame_reach C fn s0 j (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all scfg_chain_segment_advance_back >> strip_tac >>
  qexists_tac `u` >> simp[] >>
  `active_inst fn i s` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     imp_res_tac lookup_block_member_label >> fs[get_instruction_def]) >>
  `frame_reach C fn s0 i s` by metis_tac[] >>
  `u.vs_halted = s.vs_halted` by
    (qpat_assum `step_inst k C i s = OK u` (mp_then Any mp_tac step_preserves_halted) >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `step_inst k C i s = OK u` (mp_then Any mp_tac step_preserves_control_flow) >> simp[]) >>
  simp[] >> metis_tac[frame_reach_rules]
QED

Theorem scfg_step_OK_nonphi:
  step_inst k C i s = OK u ==> i.inst_opcode <> PHI
Proof
  strip_tac >> strip_tac >> Cases_on `i` >>
  gvs[step_inst_def, step_inst_base_def]
QED

Theorem scfg_chain_iprefix_rooted:
  !C bt t v. scfg_iprefix C bt t v ==>
  !fn a b s s0 bb.
    scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
    (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
    ?w bw. (scfg_chain_segment a b w v \/ scfg_chain_splice a w v) /\
      ~w.vs_halted /\ lookup_block w.vs_current_bb fn.fn_blocks = SOME bw /\
      (!i. active_inst fn i w ==> frame_reach C fn s0 i w)
Proof
  ho_match_mp_tac scfg_iprefix_ind >> conj_tac
  >- (rpt strip_tac >> qexistsl_tac [`s`, `bb`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_segment_normalize >>
  disch_then (qx_choosel_then [`s1`, `bb1`] strip_assume_tac) >>
  `i.inst_opcode <> PHI` by metis_tac[scfg_step_OK_nonphi] >>
  `get_instruction bb1 s1.vs_inst_idx = SOME i` by
    (irule scfg_chain_segment_instruction_inverse >> metis_tac[]) >>
  drule_all scfg_chain_segment_rooted_advance >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `step_inst k C i t = OK u`
      (mp_then Any mp_tac step_preserves_control_flow) >> simp[]) >>
  first_x_assum irule >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem scfg_chain_iprefix_observation:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  scfg_iprefix C bt t v /\
  get_instruction bt v.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI ==>
  ?w. frame_reach C fn s0 i w /\ scfg_payload w v /\
    mem_corr i w i v /\ call_corr i w i v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scfg_chain_iprefix_rooted >>
  disch_then (qx_choose_then `w` (qx_choose_then `bw`
    (map_every assume_tac o CONJUNCTS))) >>
  `v.vs_current_bb = t.vs_current_bb` by
    metis_tac[scfg_iprefix_current_bb] >>
  drule_all scfg_chain_segment_normalize >>
  disch_then (qx_choosel_then [`s1`, `bb1`] strip_assume_tac) >>
  `get_instruction bb1 s1.vs_inst_idx = SOME i` by
    (irule scfg_chain_segment_instruction_inverse >> metis_tac[]) >>
  `active_inst fn i s1` by
    (simp[active_inst_def] >> qexists_tac `bb1` >>
     imp_res_tac lookup_block_member_label >> fs[get_instruction_def]) >>
  `inst_wf i` by
    (irule active_inst_wf >> qexistsl_tac [`fn`, `s1`] >> simp[] >>
     metis_tac[scfg_chain_hyp_def, scfg_normalized_static, scfg_static_inst_wf]) >>
  qexists_tac `s1` >>
  metis_tac[scfg_chain_segment_payload, scfg_chain_segment_observation]
QED

Theorem scfg_chain_segment_jump:
  a.bb_label <> b.bb_label /\ scfg_chain_segment a b s t /\ l <> b.bb_label ==>
  scfg_chain_exit a b (jump_to l s) (jump_to l t)
Proof
  strip_tac >>
  `scfg_payload (jump_to l s) (jump_to l t)` by
    metis_tac[scfg_chain_segment_payload, scfg_payload_jump] >>
  fs[scfg_chain_exit_def, scfg_chain_segment_def, jump_to_def] >> gvs[]
QED

Theorem scfg_chain_segment_branch:
  a.bb_label <> b.bb_label /\ scfg_chain_segment a b s t /\
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C i s = OK (jump_to l s) /\ l <> b.bb_label ==>
  step_inst k C i t = OK (jump_to l t) /\
  scfg_chain_exit a b (jump_to l s) (jump_to l t)
Proof
  strip_tac >> reverse conj_tac >- metis_tac[scfg_chain_segment_jump] >>
  `t = scfg_ctrl t.vs_current_bb t.vs_prev_bb t.vs_inst_idx s` by
    fs[scfg_chain_segment_def, scfg_payload_def] >>
  qpat_x_assum `t = scfg_ctrl _ _ _ s` (fn th => once_rewrite_tac[th]) >>
  simp[scfg_ctrl_branch, exec_result_map_def, jump_to_def, scfg_ctrl_def]
QED
