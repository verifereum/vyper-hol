(* Coordinate-bearing observations for revert-forward frame simulation. *)
Theory simplifyCfgFrameRf
Ancestors
  simplifyCfgMergeSemantics simplifyCfgMergeSegment simplifyCfgFixupPrefixes
  simplifyCfgBypassSemantics simplifyCfgBypassPrefix simplifyCfgFragments
  simplifyCfgControl simplifyCfgDefs simplifyCfgSimTools
  simplifyCfgMergeEntry simplifyCfgMergePaths simplifyCfgMergeExec
  simplifyCfgStruct simplifyCfgStaticInterface
  simplifyCfgBypassClosure simplifyCfgBypassShape simplifyCfgBypassEntry
  simplifyCfgShapeCore simplifyCfgShape
  simplifyCfgFixupSemantics simplifyCfgPhiBlockSemantics
  simplifyCfgAvailability simplifyCfgFixupStatic simplifyCfgPhiConsumer
  simplifyCfgRestriction simplifyCfgReachuses simplifyCfgMergeClosure
  simplifyCfgBypassWrapper simplifyCfgCollapseSemantics
  simplifyCfgRoundSemantics simplifyCfgGeneratedSubst
  analysisSimProofsBase simplifyCfgFramePrefixes simplifyCfgFixupRuns unitMemInv
  venomExecSemantics venomExecProofs venomInst venomState venomWf
  o1PassLift contextCodegenRel codegenRel list rich_list

Theorem scfg_chain_iprefix_segment_observation:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  scfg_iprefix C bt t v /\
  get_instruction bt v.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI ==>
  ?w. frame_reach C fn s0 i w /\ scfg_chain_segment a b w v /\
    scfg_payload w v /\ mem_corr i w i v /\ call_corr i w i v
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

Theorem scfg_chain_rooted_segment_observation:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  eval_phis t bt.bb_instructions = OK v /\
  scfg_iprefix C bt (v with vs_inst_idx := phi_prefix_length bt.bb_instructions) w /\
  get_instruction bt w.vs_inst_idx = SOME i /\ i.inst_opcode <> PHI ==>
  ?u. frame_reach C fn s0 i u /\ scfg_chain_segment a b u w /\
    scfg_payload u w /\ mem_corr i u i w /\ call_corr i u i w
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
  irule scfg_chain_iprefix_segment_observation >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`bb`, `bt`,
    `v with vs_inst_idx := phi_prefix_length bt.bb_instructions`] >>
  goal_assum (drule_at (Pat `scfg_iprefix _ _ _ _`)) >> simp[] >>
  metis_tac[eval_phis_preserves_current_bb]
QED

(* Outside the converted ASSIGN interval, the tail witness is the target
   state itself, not merely a state with matching memory payload. *)
Theorem scfg_assign_tail_nonassign_reach:
  fb.bb_instructions = pre ++ assigns ++ tail /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  a.vs_inst_idx = LENGTH pre /\
  u.vs_inst_idx = LENGTH pre + LENGTH assigns /\
  scfg_iprefix C fb a u /\ scfg_iprefix C fb a t /\
  get_instruction fb t.vs_inst_idx = SOME j /\ j.inst_opcode <> ASSIGN /\
  get_instruction bb u.vs_inst_idx = SOME i /\ frame_reach C fn s0 i u /\
  MEM bb fn.fn_blocks /\ bb.bb_label = u.vs_current_bb /\
  (!n. u.vs_inst_idx <= n ==> get_instruction bb n = get_instruction fb n) ==>
  frame_reach C fn s0 j t
Proof
  strip_tac >>
  `~(t.vs_inst_idx < u.vs_inst_idx)` by
    (strip_tac >>
     `t.vs_inst_idx < LENGTH pre + LENGTH assigns` by decide_tac >>
     drule_all scfg_assign_interval_active >> simp[]) >>
  `scfg_iprefix C fb u t` by
    (irule scfg_iprefix_cut >> simp[] >> qexists_tac `a` >> simp[]) >>
  `scfg_iprefix C bb u t` by
    (drule scfg_iprefix_same_tail >> disch_then irule >> simp[]) >>
  `get_instruction bb t.vs_inst_idx = SOME j` by
    metis_tac[scfg_iprefix_same_tail_observe] >>
  drule scfg_iprefix_frame_reach >> disch_then irule >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem scfg_same_after_assigns_append:
  !xs p q. same_after_assigns xs p q ==>
    same_after_assigns (xs ++ ys) p q
Proof
  Induct_on `xs` >> simp[same_after_assigns_def] >> rpt strip_tac
  >- (Cases_on `ys` >> simp[same_after_assigns_def]) >>
  Cases_on `p = q` >> gvs[same_after_assigns_def] >>
  Cases_on `step_back_assign h p` >> gvs[] >>
  Cases_on `step_back_assign h q` >> gvs[]
QED

Theorem scfg_get_instruction_prepend:
  cb.bb_instructions = pre ++ bb.bb_instructions ==>
  get_instruction cb (LENGTH pre + n) = get_instruction bb n
Proof
  simp[get_instruction_def, EL_APPEND]
QED

Theorem scfg_revert_forward_pair_prepend:
  cb.bb_instructions = pre ++ bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair cb (LENGTH pre + i) (LENGTH pre + j)
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j` mp_tac >>
  rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  `!n. get_instruction cb (LENGTH pre + n) = get_instruction bb n` by
    metis_tac[scfg_get_instruction_prepend] >>
  `TAKE (LENGTH pre + i) cb.bb_instructions =
    pre ++ TAKE i bb.bb_instructions` by simp[TAKE_APPEND] >>
  `DROP (SUC (LENGTH pre + i)) cb.bb_instructions =
    DROP (SUC i) bb.bb_instructions` by
    (`SUC (LENGTH pre + i) = LENGTH pre + SUC i` by decide_tac >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `LENGTH pre <= k` by decide_tac >>
      `k = LENGTH pre + (k - LENGTH pre)` by decide_tac >>
      `get_instruction bb (k - LENGTH pre) = SOME inst` by metis_tac[] >>
      first_x_assum irule >> goal_assum (drule_at Any) >> decide_tac) >>
  `j + LENGTH pre - SUC (i + LENGTH pre) = j - SUC i` by decide_tac >>
  simp[REVERSE_APPEND] >>
  metis_tac[scfg_same_after_assigns_append]
QED

Theorem scfg_step_back_assign_image:
  (!i. i.inst_opcode = ASSIGN ==> f i = i) /\
  (!i. (f i).inst_outputs = i.inst_outputs) /\
  step_back_assign i p = SOME q ==>
  step_back_assign (f i) p = SOME q
Proof
  strip_tac >> Cases_on `p` >>
  gvs[step_back_assign_def, AllCaseEqs()] >>
  Cases_on `i.inst_opcode = ASSIGN` >> gvs[]
QED

Theorem scfg_same_after_assigns_image:
  (!i. i.inst_opcode = ASSIGN ==> f i = i) /\
  (!i. (f i).inst_outputs = i.inst_outputs) ==>
  !xs p q. same_after_assigns xs p q ==>
    same_after_assigns (MAP f xs) p q
Proof
  strip_tac >> Induct_on `xs` >> simp[same_after_assigns_def] >>
  rpt strip_tac >> Cases_on `p = q` >> gvs[] >>
  Cases_on `step_back_assign h p` >> gvs[] >>
  Cases_on `step_back_assign h q` >> gvs[] >>
  `step_back_assign (f h) p = SOME x` by
    metis_tac[scfg_step_back_assign_image] >>
  `step_back_assign (f h) q = SOME x'` by
    metis_tac[scfg_step_back_assign_image] >> simp[]
QED

Theorem scfg_get_instruction_map:
  cb.bb_instructions = MAP f bb.bb_instructions ==>
  get_instruction cb n = OPTION_MAP f (get_instruction bb n)
Proof
  simp[get_instruction_def, EL_MAP] >> strip_tac >>
  Cases_on `n < LENGTH bb.bb_instructions` >> simp[]
QED

Theorem scfg_revert_forward_pair_image_endpoints:
  (!x. x.inst_opcode = ASSIGN ==> f x = x) /\
  (!x. (f x).inst_outputs = x.inst_outputs) /\
  (!x. (get_instruction bb i = SOME x \/ get_instruction bb j = SOME x) ==>
       f x = x) /\
  cb.bb_instructions = MAP f bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair cb i j
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j` mp_tac >>
  rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  `!n. get_instruction cb n = OPTION_MAP f (get_instruction bb n)` by
    metis_tac[scfg_get_instruction_map] >>
  `!k. i < k /\ k < j ==> get_instruction cb k = get_instruction bb k` by
    (rpt strip_tac >> Cases_on `get_instruction bb k` >> simp[] >>
     `x.inst_opcode = ASSIGN` by metis_tac[] >> simp[]) >>
  `TAKE (j - SUC i) (DROP (SUC i) cb.bb_instructions) =
    TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)` by
    (`j < LENGTH bb.bb_instructions` by fs[get_instruction_def] >>
     `j - SUC i <= LENGTH bb.bb_instructions - SUC i` by decide_tac >>
     irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_DROP] >> rpt strip_tac >>
     rename1 `n < _` >> gvs[LENGTH_TAKE_EQ, LENGTH_DROP] >>
     `i < SUC i + n /\ SUC i + n < j` by decide_tac >>
     `SUC i + n < LENGTH bb.bb_instructions` by decide_tac >>
     `EL (SUC i + n) cb.bb_instructions = EL (SUC i + n) bb.bb_instructions` by
       (first_x_assum (qspec_then `SUC i + n` mp_tac) >>
        simp[get_instruction_def, EL_MAP]) >>
     gvs[EL_TAKE, EL_DROP, EL_MAP, arithmeticTheory.ADD_COMM]) >>
  `f inst1 = inst1 /\ f inst2 = inst2` by metis_tac[] >>
  `!ins. ins.inst_opcode = ASSIGN ==> f ins = ins` by simp[] >>
  simp[GSYM MAP_TAKE, GSYM MAP_REVERSE] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `z.inst_opcode = ASSIGN` by metis_tac[] >> simp[]) >>
  rpt conj_tac >> irule scfg_same_after_assigns_image >> simp[]
QED

Theorem scfg_revert_forward_pair_image:
  (!x. x.inst_opcode <> PHI /\ x.inst_opcode <> JNZ /\
       x.inst_opcode <> JMP ==> f x = x) /\
  (!x. (f x).inst_outputs = x.inst_outputs) /\
  cb.bb_instructions = MAP f bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair cb i j
Proof
  strip_tac >> irule scfg_revert_forward_pair_image_endpoints >>
  qexistsl_tac [`bb`, `f`] >> simp[] >>
  rpt strip_tac >> gvs[revert_forward_pair_def] >> metis_tac[]
QED

Theorem scfg_phi_image_revert_forward_pair:
  cb.bb_instructions = MAP (scfg_phi_image a b l) bb.bb_instructions /\
  revert_forward_pair bb i j ==> revert_forward_pair cb i j
Proof
  strip_tac >> irule scfg_revert_forward_pair_image >>
  qexistsl_tac [`bb`, `scfg_phi_image a b l`] >> simp[scfg_phi_image_nonphi]
QED

Theorem scfg_revert_forward_at_prepend:
  cb.bb_instructions = pre ++ bb.bb_instructions /\ revert_forward_at bb k ==>
  revert_forward_at cb (LENGTH pre + k)
Proof
  rewrite_tac[revert_forward_at_def] >> strip_tac >>
  qexists_tac `LENGTH pre + j`
  >- (disj1_tac >> irule scfg_revert_forward_pair_prepend >>
      goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> irule scfg_revert_forward_pair_prepend >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem scfg_chain_left_not_revert_forward:
  scfg_chain_hyp fn a b ==> ~revert_forward_at a k
Proof
  strip_tac >>
  `bb_well_formed a` by
    (drule scfg_chain_old_wf >>
     metis_tac[scfg_chain_hyp_def, lookup_block_MEM, wf_function_bb_well_formed]) >>
  `~((LAST a.bb_instructions).inst_opcode = REVERT)` by
    (drule scfg_chain_transfer_shape >> strip_tac >> simp[]) >>
  strip_tac >> fs[revert_forward_at_def, revert_forward_pair_def] >>
  `MEM inst2 a.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `inst2 = LAST a.bb_instructions` by
    (irule bb_well_formed_terminator_last >> simp[is_terminator_def]) >>
  gvs[]
QED

Theorem scfg_phi_image_revert_forward_at:
  cb.bb_instructions = MAP (scfg_phi_image a b l) bb.bb_instructions /\
  revert_forward_at bb k ==> revert_forward_at cb k
Proof
  rewrite_tac[revert_forward_at_def] >> strip_tac >> qexists_tac `j`
  >- (disj1_tac >> irule scfg_phi_image_revert_forward_pair >>
      goal_assum (drule_at Any) >> qexistsl_tac [`a`, `b`, `l`] >> simp[]) >>
  disj2_tac >> irule scfg_phi_image_revert_forward_pair >>
  goal_assum (drule_at Any) >> qexistsl_tac [`a`, `b`, `l`] >> simp[]
QED

Theorem scfg_chain_segment_revert_forward:
  scfg_chain_hyp fn a b /\ scfg_chain_segment a b s t /\
  in_revert_forward fn s ==> in_revert_forward (scfg_chain fn a b) t
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label` by
    metis_tac[scfg_chain_hyp_def, can_merge_blocks_distinct] >>
  fs[in_revert_forward_def] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  Cases_on `s.vs_current_bb = a.bb_label`
  >- (`bb = a` by metis_tac[scfg_chain_hyp_def, optionTheory.SOME_11] >>
      metis_tac[scfg_chain_left_not_revert_forward]) >>
  Cases_on `s.vs_current_bb = b.bb_label`
  >- (`bb = b` by metis_tac[scfg_chain_hyp_def, optionTheory.SOME_11] >> gvs[] >>
      `t.vs_current_bb = a.bb_label /\
       t.vs_inst_idx = LENGTH (FRONT a.bb_instructions) + s.vs_inst_idx` by
        fs[scfg_chain_segment_def] >>
      qexists_tac `scfg_chain_block a b a` >>
      `lookup_block a.bb_label fn.fn_blocks = SOME a` by fs[scfg_chain_hyp_def] >>
      simp[scfg_chain_lookup_eq] >>
      irule scfg_phi_image_revert_forward_at >>
      qexistsl_tac [`a`, `b`, `merge_blocks a b`, `a.bb_label`] >>
      simp[scfg_chain_block_def, merge_blocks_def] >>
      irule scfg_revert_forward_at_prepend >>
      goal_assum (drule_at Any) >> simp[merge_blocks_def]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx` by
    fs[scfg_chain_segment_def] >>
  qexists_tac `scfg_chain_block a b bb` >>
  simp[scfg_chain_lookup_eq] >>
  irule scfg_phi_image_revert_forward_at >>
  goal_assum (drule_at Any) >> simp[scfg_chain_block_def] >>
  qexistsl_tac [`a`, `b`, `s.vs_current_bb`] >> simp[]
QED

Theorem scfg_bypass_image_revert:
  scfg_label_positions i /\ i.inst_opcode = REVERT ==>
  scfg_bypass_image A B target l i = i
Proof
  strip_tac >>
  `EVERY (\op. ~is_label_operand op) i.inst_operands` by
    gvs[scfg_label_positions_def, unitShapeDefsTheory.label_positions_ok_def] >>
  `subst_label_inst B target i = i` by
    metis_tac[simplifyCfgShapeTheory.subst_label_inst_no_label_operands] >>
  `canon_jnz_inst i = i` by
    (Cases_on `canon_jnz_inst i = i` >> simp[] >>
     drule canon_jnz_inst_changed >> simp[]) >>
  simp[scfg_bypass_image_def, scfg_bypass_term_def, is_terminator_def,
    update_phi_bypass_def]
QED

Theorem scfg_bypass_block_revert_forward_pair:
  EVERY scfg_label_positions bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair (scfg_bypass_block a b bb) i j
Proof
  strip_tac >> irule scfg_revert_forward_pair_image_endpoints >>
  qexistsl_tac [`bb`,
    `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label`] >>
  simp[scfg_bypass_block_def] >> conj_tac
  >- (rpt strip_tac >> irule scfg_bypass_image_ordinary >> simp[is_terminator_def]) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >> gen_tac >> disch_tac >>
  `scfg_label_positions x` by
    (fs[EVERY_MEM] >> first_x_assum irule >>
     fs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  Cases_on `x.inst_opcode = REVERT`
  >- (irule scfg_bypass_image_revert >> simp[]) >>
  `x.inst_opcode = RETURNDATACOPY` by
    (gvs[revert_forward_pair_def] >> metis_tac[optionTheory.SOME_11]) >>
  irule scfg_bypass_image_ordinary >> simp[is_terminator_def]
QED

Theorem scfg_bypass_block_revert_forward_at:
  EVERY scfg_label_positions bb.bb_instructions /\ revert_forward_at bb k ==>
  revert_forward_at (scfg_bypass_block a b bb) k
Proof
  rewrite_tac[revert_forward_at_def] >> strip_tac >> qexists_tac `j`
  >- (disj1_tac >> irule scfg_bypass_block_revert_forward_pair >> simp[]) >>
  disj2_tac >> irule scfg_bypass_block_revert_forward_pair >> simp[]
QED

Theorem scfg_bypass_aligned_revert_forward:
  scfg_bypass_hyp fn a b fn' /\ scfg_bypass_aligned a b s t /\
  in_revert_forward fn s ==> in_revert_forward fn' t
Proof
  strip_tac >>
  `scfg_shape fn` by metis_tac[scfg_bypass_old_static, scfg_static_shape] >>
  fs[in_revert_forward_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `EVERY scfg_label_positions bb.bb_instructions` by
    (fs[scfg_shape_def, scfg_inst_shape_def, EVERY_MEM] >>
     metis_tac[unitLabelMapIdentityTheory.fn_insts_MEM]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
   s.vs_current_bb <> b.bb_label` by
    fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
  qexists_tac `scfg_bypass_block a b bb` >>
  conj_tac
  >- (drule scfg_bypass_lookup_eq >>
      disch_then (qspec_then `s.vs_current_bb` mp_tac) >> simp[]) >>
  simp[] >> irule scfg_bypass_block_revert_forward_at >> simp[]
QED

Theorem scfg_step_back_nonassign:
  i.inst_opcode <> ASSIGN /\ step_back_assign i p = SOME q ==> q = p
Proof
  Cases_on `p` >> simp[step_back_assign_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem scfg_same_after_nonassigns:
  !ps p q. EVERY (\i. i.inst_opcode <> ASSIGN) ps ==>
    (same_after_assigns ps p q <=> p = q)
Proof
  Induct_on `ps` >> simp[same_after_assigns_def] >> rpt strip_tac >>
  Cases_on `p = q` >> simp[] >>
  Cases_on `step_back_assign h p` >> simp[] >>
  Cases_on `step_back_assign h q` >> simp[] >>
  metis_tac[scfg_step_back_nonassign]
QED

Theorem scfg_same_after_assigns_erase:
  EVERY (\i. i.inst_opcode <> ASSIGN) ps ==>
  !xs p q. same_after_assigns (xs ++ ps) p q ==> same_after_assigns xs p q
Proof
  strip_tac >> Induct_on `xs`
  >- simp[scfg_same_after_nonassigns, same_after_assigns_def] >>
  simp[same_after_assigns_def] >> rpt strip_tac >>
  Cases_on `p = q` >> gvs[] >>
  Cases_on `step_back_assign h p` >> gvs[] >>
  Cases_on `step_back_assign h q` >> gvs[]
QED

Theorem scfg_same_after_assigns_replace:
  EVERY (\i. i.inst_opcode <> ASSIGN) ps /\
  same_after_assigns (xs ++ ps) p q ==> same_after_assigns (xs ++ qs) p q
Proof
  metis_tac[scfg_same_after_assigns_erase, scfg_same_after_assigns_append]
QED

Theorem scfg_phi_prefix_endpoint_bound:
  bb.bb_instructions = ps ++ tail /\ EVERY (\x. x.inst_opcode = PHI) ps /\
  get_instruction bb n = SOME i /\ i.inst_opcode <> PHI ==> LENGTH ps <= n
Proof
  strip_tac >> spose_not_then assume_tac >>
  `n < LENGTH ps` by decide_tac >>
  `EL n ps = i` by gvs[get_instruction_def, EL_APPEND] >>
  fs[EVERY_EL] >> metis_tac[]
QED

Theorem scfg_revert_forward_pair_prefix_replace:
  bb.bb_instructions = ps ++ tail /\ cb.bb_instructions = qs ++ tail /\
  EVERY (\x. x.inst_opcode = PHI) ps /\ LENGTH qs = LENGTH ps /\
  revert_forward_pair bb i j ==> revert_forward_pair cb i j
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j` mp_tac >>
  rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  `LENGTH ps <= i /\ LENGTH ps <= j` by
    (conj_tac >> irule scfg_phi_prefix_endpoint_bound >>
     simp[] >> qexists_tac `bb` >> simp[] >> metis_tac[]) >>
  `!n. LENGTH ps <= n ==> get_instruction cb n = get_instruction bb n` by
    (simp[get_instruction_def, EL_APPEND] >> rpt strip_tac >>
     `~(n < LENGTH ps)` by decide_tac >> simp[]) >>
  `TAKE i bb.bb_instructions = ps ++ TAKE (i - LENGTH ps) tail /\
   TAKE i cb.bb_instructions = qs ++ TAKE (i - LENGTH ps) tail` by
    simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  `DROP (SUC i) cb.bb_instructions = DROP (SUC i) bb.bb_instructions` by
    simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  `EVERY (\x. x.inst_opcode <> ASSIGN) (REVERSE ps)` by
    (fs[EVERY_REVERSE, EVERY_MEM] >> metis_tac[]) >>
  simp[REVERSE_APPEND] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  rpt conj_tac >> irule scfg_same_after_assigns_replace >>
  goal_assum (drule_at Any) >> gvs[REVERSE_APPEND]
QED

Theorem scfg_fix_phis_revert_forward_pair:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\x. x.inst_opcode = PHI) ps /\
  EVERY (\x. x.inst_opcode <> PHI) tail /\ revert_forward_pair bb i j ==>
  revert_forward_pair (fix_phis_in_block actual_preds bb) i j
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `revert_forward_pair cb i j` >>
  `cb.bb_instructions =
    (MAP (fix_phi_inst actual_preds) (FILTER (\x. (fix_phi_inst actual_preds x).inst_opcode = PHI) ps) ++
     MAP (fix_phi_inst actual_preds) (FILTER (\x. (fix_phi_inst actual_preds x).inst_opcode <> PHI) ps)) ++ tail` by
    (simp[Abbr `cb`] >>
     metis_tac[simplifyCfgPhiBlockSemanticsTheory.scfg_fix_phis_partition_instructions,
       APPEND_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `cb.bb_instructions = qs ++ tail` >>
  `LENGTH qs = LENGTH ps` by
    (`LENGTH cb.bb_instructions = LENGTH bb.bb_instructions` by
      (qunabbrev_tac `cb` >>
       irule simplifyCfgFixupStaticTheory.scfg_fix_phis_length >>
       qexistsl_tac [`ps`, `tail`] >> simp[]) >>
     gvs[LENGTH_APPEND]) >>
  irule scfg_revert_forward_pair_prefix_replace >>
  goal_assum (drule_at Any) >> qexistsl_tac [`bb`, `tail`] >> simp[]
QED

Theorem scfg_fix_phis_revert_forward_at:
  bb_well_formed bb /\ revert_forward_at bb k ==>
  revert_forward_at (fix_phis_in_block actual_preds bb) k
Proof
  strip_tac >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `bb.bb_instructions = ps ++ tail` by simp[Abbr `ps`, Abbr `tail`] >>
  `EVERY (\x. x.inst_opcode = PHI) ps` by
    simp[Abbr `ps`, analysisSimProofsBaseTheory.phi_prefix_all_phi] >>
  `EVERY (\x. x.inst_opcode <> PHI) tail` by
    (simp[Abbr `tail`] >>
     irule simplifyCfgFixupStaticTheory.scfg_phi_suffix_nonphi >>
     fs[bb_well_formed_def]) >>
  fs[revert_forward_at_def] >> qexists_tac `j`
  >- (disj1_tac >> irule scfg_fix_phis_revert_forward_pair >>
      simp[] >> qexistsl_tac [`ps`, `tail`] >> simp[]) >>
  disj2_tac >> irule scfg_fix_phis_revert_forward_pair >>
  simp[] >> qexistsl_tac [`ps`, `tail`] >> simp[]
QED

Theorem scfg_fix_all_phis_revert_forward:
  wf_function fn /\ in_revert_forward fn s ==>
  in_revert_forward (fix_all_phis fn) s
Proof
  strip_tac >> fs[in_revert_forward_def] >>
  `bb_well_formed bb` by
    metis_tac[lookup_block_MEM, wf_function_bb_well_formed] >>
  qexists_tac `fix_phis_in_block (pred_labels fn bb.bb_label) bb` >>
  simp[simplifyCfgFixupSemanticsTheory.scfg_fix_all_phis_lookup] >>
  irule scfg_fix_phis_revert_forward_at >> simp[]
QED

Theorem scfg_frame_sim_rf_ctx_bisim:
  ctx_bisim C C' ==> frame_sim_rf L C C' fn fn
Proof
  strip_tac >> simp[frame_sim_rf_def] >> rpt strip_tac >>
  qexistsl_tac [`inst'`, `s'`] >> simp[mem_corr_refl] >>
  metis_tac[frame_reach_ctx_bisim]
QED

Theorem scfg_restriction_frame_sim_rf:
  wf_function fn ==> frame_sim_rf L C C fn (remove_unreachable_blocks fn)
Proof
  strip_tac >> simp[frame_sim_rf_def] >> rpt strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `frame_reach C fn s0 inst' s'` by
    metis_tac[simplifyCfgRestrictionSemanticsTheory.scfg_restriction_frame_reach_back] >>
  `active_inst (remove_unreachable_blocks fn) inst' s'` by
    metis_tac[frame_reach_active] >>
  `?bb. lookup_block s'.vs_current_bb (remove_unreachable_blocks fn).fn_blocks = SOME bb` by
    (fs[active_inst_def] >>
     metis_tac[MEM_lookup_block, remove_unreachable_blocks_wf, wf_function_def, fn_labels_def]) >>
  qexistsl_tac [`inst'`, `s'`] >> simp[mem_corr_refl] >>
  strip_tac >> fs[in_revert_forward_def] >>
  `lookup_block s'.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[simplifyCfgRestrictionTheory.scfg_restriction_lookup_back] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem scfg_fix_phis_snapshot_nonassign_reach:
  bb.bb_instructions = ps ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) ps /\
  EVERY (\i. i.inst_opcode <> PHI) tail /\ tail <> [] /\
  rs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst actual_preds i).inst_opcode <> PHI) ps /\
  EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst actual_preds) cs) /\
  eval_phis s ps = OK u /\
  eval_phis s (MAP (fix_phi_inst actual_preds) rs) = OK v /\
  scfg_iprefix C (fix_phis_in_block actual_preds bb)
    (v with vs_inst_idx := LENGTH rs) (u with vs_inst_idx := LENGTH rs + LENGTH cs) /\
  fb = fix_phis_in_block actual_preds bb /\ eval_phis s fb.bb_instructions = OK w /\
  a = w with vs_inst_idx := phi_prefix_length fb.bb_instructions /\
  scfg_iprefix C fb a t /\ get_instruction fb t.vs_inst_idx = SOME j /\
  j.inst_opcode <> ASSIGN /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  frame_reach C fn s0 j t
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst actual_preds) rs) /\
   EVERY (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst actual_preds) cs ++ tail) /\
   LENGTH rs + LENGTH cs = LENGTH ps` by
    (irule scfg_fix_phis_prefix_shape >> metis_tac[]) >>
  `fb.bb_instructions = MAP (fix_phi_inst actual_preds) rs ++
      (MAP (fix_phi_inst actual_preds) cs ++ tail)` by
    metis_tac[scfg_fix_phis_partition_instructions, APPEND_ASSOC] >>
  `w = v /\ phi_prefix_length fb.bb_instructions = LENGTH rs` by
    (qpat_x_assum `eval_phis s fb.bb_instructions = OK w` mp_tac >>
     qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
     simp[Excl "APPEND_ASSOC", scfg_eval_phis_append, scfg_phi_prefix_append]) >>
  `phi_prefix_length bb.bb_instructions = LENGTH ps` by
    simp[scfg_phi_prefix_append] >>
  `get_instruction bb (LENGTH ps) = SOME (HD tail)` by
    (Cases_on `tail` >> gvs[get_instruction_def, EL_APPEND]) >>
  `frame_reach C fn s0 (HD tail) (u with vs_inst_idx := LENGTH ps)` by
    (irule scfg_rooted_prefix_frame_reach >>
     qexistsl_tac [`u with vs_inst_idx := LENGTH ps`, `bb`, `s`, `u`] >>
     simp[scfg_iprefix_rules, TAKE_APPEND]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
  `u.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qpat_x_assum `rs = _` kall_tac >> qpat_x_assum `cs = _` kall_tac >>
  irule scfg_assign_tail_nonassign_reach >> simp[] >>
  qexistsl_tac [`a`, `MAP (fix_phi_inst actual_preds) cs`, `bb`, `fb`,
    `HD tail`, `MAP (fix_phi_inst actual_preds) rs`, `tail`,
    `u with vs_inst_idx := LENGTH ps`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule scfg_fix_phis_tail_lookup >> metis_tac[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem scfg_rooted_fix_phis_nonassign_reach:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) /\
  fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  fb = fix_phis_in_block (pred_labels fn bb.bb_label) bb /\
  eval_phis s fb.bb_instructions = OK v /\
  a = v with vs_inst_idx := phi_prefix_length fb.bb_instructions /\
  scfg_iprefix C fb a t /\ get_instruction fb t.vs_inst_idx = SOME j /\
  j.inst_opcode <> ASSIGN ==>
  frame_reach C fn s0 j t
Proof
  strip_tac >> drule_all scfg_bprefix_incoming >> strip_tac
  >- (gvs[] >> drule_all scfg_entry_block_no_phi >> strip_tac >>
      `fix_phis_in_block (pred_labels fn bb.bb_label) bb = bb` by
        metis_tac[scfg_fix_phis_no_phi] >>
      irule scfg_rooted_prefix_frame_reach >>
      qexistsl_tac [`v with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
        `bb`, `s`, `v`] >> gvs[] >>
      metis_tac[scfg_eval_phis_take_prefix]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  qabbrev_tac `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  qabbrev_tac `tail = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions` >>
  `bb.bb_instructions = ps ++ tail` by simp[Abbr `ps`, Abbr `tail`] >>
  `EVERY (\i. i.inst_opcode = PHI) ps` by
    metis_tac[phi_prefix_all_phi] >>
  `EVERY (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> NOP) ps /\
   EVERY (\i. i.inst_opcode <> PHI) tail` by
    (irule scfg_fn_fix_phis_parts >> simp[Abbr `ps`, Abbr `tail`] >> metis_tac[]) >>
  `tail <> []` by
    (irule scfg_phi_tail_nonempty >> fs[wf_function_def] >> metis_tac[]) >>
  qabbrev_tac `rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps` >>
  qabbrev_tac `cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps` >>
  `EVERY (\i. i.inst_opcode = ASSIGN) (MAP (fix_phi_inst (pred_labels fn bb.bb_label)) cs)` by
    (irule scfg_converted_assigns >> simp[Abbr `cs`] >> metis_tac[]) >>
  `ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
   rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps /\
   cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps` by
    simp[Abbr `ps`, Abbr `rs`, Abbr `cs`] >>
  `fn_reachable fn bb.bb_label /\
   (!qb. MEM qb fn.fn_blocks /\ MEM bb.bb_label (bb_succs qb) ==> fn_reachable fn qb.bb_label)` by
    metis_tac[] >>
  drule_all scfg_fn_fix_phis_block >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  irule scfg_fix_phis_snapshot_nonassign_reach >> (conj_tac >- asm_rewrite_tac[]) >>
  qexistsl_tac [`a`, `pred_labels fn bb.bb_label`, `bb`, `cs`, `fb`, `ps`, `rs`, `s`, `tail`] >>
  metis_tac[]
QED

Theorem scfg_fix_all_phis_frame_sim_rf:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) ==>
  frame_sim_rf L C C fn (fix_all_phis fn)
Proof
  strip_tac >> simp[frame_sim_rf_def] >> rpt strip_tac >>
  `inst'.inst_opcode <> ASSIGN` by
    (strip_tac >> gvs[inst_mem_ranges_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `wf_function (fix_all_phis fn)` by metis_tac[fix_all_phis_wf] >>
  drule_all scfg_frame_reach_decompose >> strip_tac >>
  `scfg_bprefix C fn s0 s` by
    (irule scfg_fix_all_phis_bprefix_backward >> simp[] >>
     metis_tac[scfg_bprefix_rules]) >>
  qpat_x_assum `lookup_block _ _ = _` mp_tac >>
  rewrite_tac[scfg_fix_all_phis_lookup] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  strip_tac >> gvs[] >>
  `frame_reach C fn s0 inst' s'` by
    (irule scfg_rooted_fix_phis_nonassign_reach >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`inst'`, `s'`] >> simp[mem_corr_refl] >>
  metis_tac[scfg_fix_all_phis_revert_forward]
QED

Theorem scfg_cleanup_frame_sim_rf:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn ==>
  frame_sim_rf L C C fn (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> irule frame_sim_rf_trans >>
  qexistsl_tac [`C`, `remove_unreachable_blocks fn`] >>
  simp[remove_unreachable_blocks_entry, scfg_restriction_frame_sim_rf] >>
  irule scfg_fix_all_phis_frame_sim_rf >>
  simp[remove_unreachable_blocks_wf,
    simplifyCfgDefsTheory.remove_unreachable_blocks_fn_inst_wf,
    scfg_restriction_ok] >>
  rpt strip_tac >> irule scfg_restriction_blocks_reachable >>
  Cases_on `fn.fn_blocks` >>
  fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
  metis_tac[]
QED

Theorem scfg_chain_frame_sim_rf:
  scfg_chain_hyp fn a b ==> frame_sim_rf L C C fn (scfg_chain fn a b)
Proof
  strip_tac >> simp[frame_sim_rf_def] >> qx_genl_tac [`s0`, `j`, `w`] >> strip_tac >>
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
  drule_all scfg_chain_rooted_segment_observation >>
  disch_then (qx_choose_then `u1` strip_assume_tac) >>
  qexistsl_tac [`j`, `u1`] >> simp[] >>
  metis_tac[scfg_chain_segment_revert_forward]
QED

Theorem scfg_bypass_frame_sim_rf:
  ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' ==>
  frame_sim_rf L C C' fn fn'
Proof
  strip_tac >> simp[frame_sim_rf_def] >> rpt strip_tac >>
  drule_all scfg_bypass_initial_aligned >> strip_tac >>
  drule_all scfg_bypass_rooted_observe >> strip_tac >>
  `active_inst fn i u` by metis_tac[frame_reach_active] >>
  drule_all scfg_bypass_image_observations >> strip_tac >>
  qexistsl_tac [`i`, `u`] >> gvs[] >>
  metis_tac[scfg_bypass_aligned_revert_forward]
QED

Theorem scfg_try_bypass_frame_sim_rf:
  scfg_normalized fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  try_bypass fn lm bb candidates = (fn',lm',changed) ==>
  frame_sim_rf L C C fn fn'
Proof
  strip_tac >> drule_all scfg_try_bypass_choice >> strip_tac
  >- (gvs[] >> irule scfg_frame_sim_rf_ctx_bisim >> simp[ctx_bisim_refl]) >>
  irule scfg_bypass_frame_sim_rf >> metis_tac[ctx_bisim_refl]
QED

Theorem scfg_collapse_rf_trans:
  scfg_collapse_contract f g /\ frame_sim_rf L C C f g /\
  frame_sim_rf L C C g h ==> frame_sim_rf L C C f h
Proof
  strip_tac >> irule frame_sim_rf_trans >>
  qexistsl_tac [`C`, `g`] >> fs[scfg_collapse_contract_def]
QED

Theorem scfg_collapse_rf_joint:
  (!fn lm visited lbl. scfg_normalized fn ==>
    frame_sim_rf L C C fn (FST (collapse_dfs fn lm visited lbl))) /\
  (!fn lm visited succs. scfg_normalized fn ==>
    frame_sim_rf L C C fn (FST (collapse_dfs_succs fn lm visited succs)))
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume scfg_collapse_rf_joint[dfs]:
  rpt strip_tac >> simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- simp[scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  namedCases_on `bb_succs bb` ["", "s1 rest"]
  >- (Cases_on `MEM lbl visited`
      >- simp[try_bypass_def, scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl] >>
      gvs[try_bypass_def]) >>
  namedCases_on `rest` ["", "s2 rest2"]
  >- (Cases_on `lookup_block s1 fn.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> simp[scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl]) >>
      rename1 `lookup_block s1 fn.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks fn bb next_bb`
      >- suspend "merge" >>
      Cases_on `MEM lbl visited`
      >- simp[scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl] >> gvs[]) >>
  suspend "bypass"
QED

Resume scfg_collapse_rf_joint[merge]:
  gvs[] >>
  `next_bb.bb_label = s1` by metis_tac[lookup_block_member_label] >>
  `scfg_chain_hyp fn bb next_bb` by
    (simp[scfg_chain_hyp_def] >> metis_tac[]) >>
  drule scfg_collapse_chain >> strip_tac >>
  gvs[GSYM scfg_chain_def] >>
  irule scfg_collapse_rf_trans >>
  qexists_tac `scfg_chain fn bb next_bb` >>
  simp[scfg_chain_frame_sim_rf] >> first_x_assum irule >>
  fs[scfg_collapse_contract_def]
QED

Resume scfg_collapse_rf_joint[bypass]:
  Cases_on `try_bypass fn lm bb (s1::s2::rest2)` >> PairCases_on `r` >>
  `scfg_collapse_contract fn q` by
    (irule scfg_collapse_bypass >> simp[] >>
     qexistsl_tac [`bb`, `s1::s2::rest2`, `r1`, `lm`, `r0`] >> simp[]) >>
  `frame_sim_rf L C C fn q` by
    (irule scfg_try_bypass_frame_sim_rf >> simp[] >>
     qexistsl_tac [`bb`, `s1::s2::rest2`, `r1`, `lm`, `r0`] >> simp[]) >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  Cases_on `r1` >> gvs[]
  >- metis_tac[scfg_collapse_rf_trans] >>
  Cases_on `MEM bb.bb_label visited` >> gvs[] >>
  metis_tac[scfg_collapse_rf_trans]
QED

Resume scfg_collapse_rf_joint[nil]:
  simp[collapse_dfs_def, scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl]
QED

Resume scfg_collapse_rf_joint[succs]:
  rpt strip_tac >> simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm visited lbl` >> PairCases_on `r` >>
  gvs[] >>
  `scfg_collapse_contract fn q` by metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  metis_tac[scfg_collapse_rf_trans]
QED

Finalise scfg_collapse_rf_joint

Theorem scfg_round_frame_sim_rf:
  scfg_static fn ==>
  frame_sim_rf L C C fn (FST (simplify_cfg_round_with_labels fn))
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- (fs[scfg_static_def, wf_function_def, fn_has_entry_def,
         fn_entry_label_def, entry_block_def] >> Cases_on `fn.fn_blocks` >> gvs[]) >>
  qabbrev_tac `clean = fix_all_phis (remove_unreachable_blocks fn)` >>
  `scfg_collapse_contract fn clean` by metis_tac[scfg_cleanup_contract] >>
  `frame_sim_rf L C C fn clean` by
    (simp[Abbr `clean`] >> irule scfg_cleanup_frame_sim_rf >> fs[scfg_static_def]) >>
  `scfg_normalized clean` by fs[scfg_collapse_contract_def] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `scfg_collapse_contract clean q` by metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `frame_sim_rf L C C clean q` by metis_tac[scfg_collapse_rf_joint, pairTheory.FST] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  `ALL_DISTINCT (fn_labels clean)` by
    fs[scfg_normalized_def, scfg_static_def, wf_function_def, fn_labels_def] >>
  `subst_block_labels_fn r0 q = q` by metis_tac[scfg_collapse_subst_identity] >>
  `frame_sim_rf L C C q (fix_all_phis (remove_unreachable_blocks q))` by
    (irule scfg_cleanup_frame_sim_rf >>
     metis_tac[scfg_normalized_static, scfg_static_def]) >>
  Cases_on `r0 = []` >>
  gvs[simplify_cfg_round_with_labels_def, Abbr `clean`] >>
  metis_tac[scfg_collapse_rf_trans]
QED

Theorem scfg_iter_frame_sim_rf:
  !n fn. scfg_static fn ==>
  frame_sim_rf L C C fn (FST (simplify_cfg_iter_with_labels n fn))
Proof
  Induct
  >- simp[simplify_cfg_iter_with_labels_def, scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl] >>
  gen_tac >> disch_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  `scfg_collapse_contract fn q` by metis_tac[scfg_round_contract, pairTheory.FST] >>
  `frame_sim_rf L C C fn q` by metis_tac[scfg_round_frame_sim_rf, pairTheory.FST] >>
  Cases_on `q.fn_blocks = fn.fn_blocks`
  >- simp[simplify_cfg_iter_with_labels_def, scfg_frame_sim_rf_ctx_bisim, ctx_bisim_refl] >>
  `scfg_static q` by
    metis_tac[scfg_collapse_contract_def, scfg_normalized_static] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  gvs[simplify_cfg_iter_with_labels_def] >>
  metis_tac[scfg_collapse_rf_trans]
QED
