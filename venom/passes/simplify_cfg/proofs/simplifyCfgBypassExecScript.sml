(* Local instruction and transfer boundaries for jump bypass. *)
Theory simplifyCfgBypassExec
Ancestors
  simplifyCfgShapeCore
  simplifyCfgBypassEntry simplifyCfgBypassShape simplifyCfgBypassClosure
  simplifyCfgBypassStatic simplifyCfgBypassPrecondition simplifyCfgStaticInterface
  simplifyCfgMergeExec simplifyCfgControlExec simplifyCfgControlState
  simplifyCfgControl simplifyCfgDefs simplifyCfgFragments
  venomExecSemantics venomExecProofs venomInst venomState venomWf
  contextCodegenRel o1PassLift instIdxIndep list rich_list cfgTransform
  unitLabelMapIdentity unitShapeDefs simplifyCfgSimTools
  simplifyCfgDataflow

Theorem scfg_bypass_instruction:
  get_instruction (scfg_bypass_block a b bb) n =
  OPTION_MAP (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label)
    (get_instruction bb n)
Proof
  simp[scfg_bypass_block_def, get_instruction_def, EL_MAP] >>
  IF_CASES_TAC >> simp[]
QED

Theorem scfg_bypass_instruction_ordinary:
  get_instruction bb n = SOME i /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  get_instruction (scfg_bypass_block a b bb) n = SOME i
Proof
  simp[scfg_bypass_instruction, scfg_bypass_image_ordinary]
QED

Theorem scfg_bypass_active_ordinary:
  scfg_bypass_hyp fn a b fn' /\ scfg_bypass_aligned a b s t /\
  active_inst fn i s /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  active_inst fn' i t
Proof
  strip_tac >>
  `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  fs[active_inst_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all MEM_lookup_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i` by simp[get_instruction_def] >>
  drule scfg_bypass_lookup_eq >>
  disch_then (qspec_then `s.vs_current_bb` assume_tac) >>
  gvs[scfg_bypass_aligned_def] >>
  `MEM (scfg_bypass_block a b bb) fn'.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  qexists_tac `scfg_bypass_block a b bb` >>
  simp[scfg_ctrl_def, scfg_bypass_block_def, EL_MAP, scfg_bypass_image_ordinary]
QED

Theorem scfg_bypass_singleton_shape:
  scfg_bypass_hyp fn a b fn' ==>
  b.bb_instructions = [LAST b.bb_instructions] /\
  (((LAST b.bb_instructions).inst_opcode = JMP /\
    (LAST b.bb_instructions).inst_operands = [Label (HD (bb_succs b))]) \/
   (?c. (LAST b.bb_instructions).inst_opcode = JNZ /\
    (LAST b.bb_instructions).inst_operands = [c; Label (HD (bb_succs b)); Label (HD (bb_succs b))] /\
    ~is_label_operand c))
Proof
  strip_tac >>
  `LENGTH b.bb_instructions = 1 /\ MEM b fn.fn_blocks /\
   fn_inst_wf fn /\ scfg_shape fn` by
    metis_tac[scfg_bypass_hyp_def, can_bypass_jump_def, lookup_block_member_label,
      scfg_bypass_old_static, scfg_static_inst_wf, scfg_static_shape] >>
  `?i. b.bb_instructions = [i]` by
    (Cases_on `b.bb_instructions` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `inst_wf i /\ scfg_inst_shape i` by
    (fs[fn_inst_wf_def, scfg_shape_def, EVERY_MEM] >> metis_tac[fn_insts_MEM, MEM]) >>
  gvs[] >> irule scfg_single_successor_transfer >> simp[] >>
  fs[scfg_bypass_hyp_def, bb_succs_def] >> gvs[]
QED

Theorem scfg_bypass_singleton_step:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST b.bb_instructions) s ==>
  step_inst k C (LAST b.bb_instructions) s = OK (jump_to (HD (bb_succs b)) s)
Proof
  strip_tac >> drule scfg_bypass_singleton_shape >> strip_tac >>
  pop_assum strip_assume_tac
  >- (Cases_on `LAST b.bb_instructions` >> gvs[] >>
      simp[step_inst_def, step_inst_base_def]) >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf,
      scfg_static_inst_wf, scfg_static_ok, simplify_cfg_fn_ok_def] >>
  `(LAST b.bb_instructions).inst_opcode <> PHI /\
   MEM c (LAST b.bb_instructions).inst_operands` by simp[] >>
  drule_all scfg_frame_eval_nonlabel >> strip_tac >>
  Cases_on `LAST b.bb_instructions` >>
  Cases_on `eval_operand c s` >> gvs[] >>
  simp[step_inst_def, step_inst_base_def]
QED

Theorem scfg_bypass_ordinary_result:
  scfg_bypass_aligned a b s t ==>
  scfg_result (step_inst k C i s) (step_inst k C i t)
Proof
  simp[scfg_bypass_aligned_def] >> strip_tac >>
  irule scfg_ctrl_step_result
QED

Theorem scfg_bypass_ordinary_step_OK:
  scfg_bypass_aligned a b s t /\ ~is_terminator i.inst_opcode /\
  step_inst k C i s = OK u ==>
  step_inst k C i t = OK
    (scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s.vs_inst_idx u)
Proof
  strip_tac >> fs[scfg_bypass_aligned_def] >> irule scfg_ctrl_step_OK >>
  Cases_on `i.inst_opcode` >> gvs[is_terminator_def]
QED

Theorem scfg_bypass_singleton_run:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST b.bb_instructions) s /\ s.vs_inst_idx = 0 ==>
  run_block k C b s =
    if s.vs_halted then Halt (jump_to (HD (bb_succs b)) s)
    else OK (jump_to (HD (bb_succs b)) s)
Proof
  strip_tac >> drule scfg_bypass_singleton_shape >> strip_tac >>
  `is_terminator (LAST b.bb_instructions).inst_opcode /\
   (LAST b.bb_instructions).inst_opcode <> PHI` by
    (gvs[is_terminator_def] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    (qpat_assum `b.bb_instructions = [_]` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `phi_prefix_length b.bb_instructions = 0` by
    metis_tac[no_phis_phi_prefix_length_zero] >>
  drule_all scfg_bypass_singleton_step >> disch_then (qspec_then `k` assume_tac) >>
  simp[run_block_def, eval_phis_no_phis] >>
  once_rewrite_tac[exec_block_def] >> simp[get_instruction_def] >>
  qpat_assum `b.bb_instructions = [_]` (fn th => once_rewrite_tac[th]) >>
  simp[jump_to_def]
QED

Theorem scfg_bypass_source_shape:
  scfg_bypass_hyp fn a b fn' ==>
  ?c l r. (LAST a.bb_instructions).inst_opcode = JNZ /\
    (LAST a.bb_instructions).inst_operands = [c; Label l; Label r] /\
    ~is_label_operand c /\ l <> r
Proof
  strip_tac >>
  `num_succs a = 2 /\ MEM a fn.fn_blocks /\
   fn_inst_wf fn /\ scfg_shape fn` by
    metis_tac[scfg_bypass_hyp_def, can_bypass_jump_def, lookup_block_member_label,
      scfg_bypass_old_static, scfg_static_inst_wf, scfg_static_shape] >>
  `a.bb_instructions <> []` by
    (Cases_on `a.bb_instructions` >> gvs[num_succs_def, bb_succs_def]) >>
  `inst_wf (LAST a.bb_instructions) /\ scfg_inst_shape (LAST a.bb_instructions)` by
    (fs[fn_inst_wf_def, scfg_shape_def, EVERY_MEM] >> metis_tac[fn_insts_MEM, LAST_MEM]) >>
  `LENGTH (nub (REVERSE (get_successors (LAST a.bb_instructions)))) = 2` by
    (Cases_on `a.bb_instructions` >> gvs[num_succs_def, bb_succs_def]) >>
  qpat_x_assum `scfg_bypass_hyp _ _ _ _` kall_tac >>
  qpat_x_assum `fn_inst_wf _` kall_tac >>
  qpat_x_assum `scfg_shape _` kall_tac >>
  Cases_on `(LAST a.bb_instructions).inst_opcode` >>
  gvs[get_successors_def, is_terminator_def] >>
  gvs[scfg_inst_shape_def, inst_wf_def, scfg_label_positions_def, label_positions_ok_def, get_label_def] >>
  gvs[scfg_nonlabel_get_label, scfg_nonlabel_successors, listTheory.nub_def] >>
  spose_not_then assume_tac >> gvs[]
QED


Theorem scfg_step_jmp:
  i.inst_opcode = JMP /\ i.inst_operands = [Label l] ==>
  step_inst k C i s = OK (jump_to l s)
Proof
  strip_tac >> Cases_on `i` >> gvs[] >>
  simp[step_inst_def, step_inst_base_def]
QED

Theorem scfg_step_jnz:
  i.inst_opcode = JNZ /\ i.inst_operands = [c; Label l; Label r] /\
  eval_operand c s = SOME v ==>
  step_inst k C i s = OK (jump_to (if v = 0w then r else l) s)
Proof
  strip_tac >> Cases_on `i` >> gvs[] >>
  simp[step_inst_def, step_inst_base_def] >>
  Cases_on `v = 0w` >> simp[]
QED

Theorem scfg_bypass_jnz_step:
  i.inst_opcode = JNZ /\ i.inst_operands = [c; Label l; Label r] /\
  ~is_label_operand c /\ eval_operand c s = SOME v ==>
  step_inst k C (scfg_bypass_term B target i) (scfg_ctrl cur prev n s) =
    OK (jump_to (if (if v = 0w then r else l) = B then target
                 else if v = 0w then r else l) (scfg_ctrl cur prev n s))
Proof
  strip_tac >>
  `eval_operand c (scfg_ctrl cur prev n s) = SOME v` by simp[] >>
  drule_at (Pos last) scfg_step_jnz >> disch_then assume_tac >>
  Cases_on `l = B` >> Cases_on `r = B` >> Cases_on `v = 0w` >>
  simp[scfg_bypass_term_def, is_terminator_def,
       subst_label_inst_def, scfg_subst_nonlabel, subst_label_op_def,
       canon_jnz_inst_def] >>
  rpt IF_CASES_TAC >> simp[scfg_step_jmp] >>
  gvs[] >> first_x_assum irule >> simp[]
QED

Theorem scfg_bypass_source_step:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST a.bb_instructions) s ==>
  ?l. step_inst k C (LAST a.bb_instructions) s = OK (jump_to l s) /\
      step_inst k' C' (scfg_bypass_term b.bb_label (HD (bb_succs b))
        (LAST a.bb_instructions)) (scfg_ctrl cur prev n s) =
      OK (jump_to (if l = b.bb_label then HD (bb_succs b) else l)
            (scfg_ctrl cur prev n s))
Proof
  strip_tac >> drule scfg_bypass_source_shape >> strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf,
      scfg_static_inst_wf, scfg_static_ok, simplify_cfg_fn_ok_def] >>
  `(LAST a.bb_instructions).inst_opcode <> PHI /\
   MEM c (LAST a.bb_instructions).inst_operands` by simp[] >>
  drule_all scfg_frame_eval_nonlabel >> strip_tac >>
  Cases_on `eval_operand c s` >> gvs[] >>
  rename1 `eval_operand c s = SOME v` >>
  qexists_tac `if v = 0w then r else l` >> conj_tac
  >- (irule scfg_step_jnz >> simp[]) >>
  irule scfg_bypass_jnz_step >> simp[]
QED

Theorem scfg_bypass_ordinary_step_back:
  ctx_bisim C C' /\ scfg_bypass_aligned a b s t /\
  ~is_terminator i.inst_opcode /\ step_inst k' C' i t = OK v ==>
  ?k u. step_inst k C i s = OK u /\
    v = scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s.vs_inst_idx u
Proof
  strip_tac >>
  `scfg_result (step_inst k' C' i s) (OK v)` by
    metis_tac[scfg_bypass_ordinary_result] >>
  Cases_on `step_inst k' C' i s` >> gvs[scfg_result_def] >>
  drule_all scfg_bypass_ordinary_step_OK >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst k' C' i t = _` kall_tac >>
  drule_all ctx_bisim_step_ok >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem scfg_bypass_jump_aligned:
  a.bb_label <> b.bb_label /\ target <> b.bb_label /\
  s.vs_current_bb = a.bb_label ==>
  scfg_bypass_aligned a b
    (if l = b.bb_label then jump_to target (jump_to l s) else jump_to l s)
    (jump_to (if l = b.bb_label then target else l)
       (scfg_ctrl a.bb_label prev n s))
Proof
  strip_tac >> Cases_on `l = b.bb_label` >>
  simp[scfg_bypass_aligned_def, jump_to_def, scfg_ctrl_def]
QED

Theorem scfg_bypass_source_successor:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST a.bb_instructions) s /\
  s.vs_current_bb = a.bb_label ==>
  ?l t. step_inst k C (LAST a.bb_instructions) s = OK (jump_to l s) /\
    step_inst k' C' (scfg_bypass_term b.bb_label (HD (bb_succs b))
      (LAST a.bb_instructions)) (scfg_ctrl a.bb_label prev n s) = OK t /\
    scfg_bypass_aligned a b
      (if l = b.bb_label then jump_to (HD (bb_succs b)) (jump_to l s)
       else jump_to l s) t
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label /\ HD (bb_succs b) <> b.bb_label` by
    (fs[scfg_bypass_hyp_def] >>
     metis_tac[can_bypass_jump_labels_distinct, scfg_bypass_target_distinct, HD]) >>
  metis_tac[scfg_bypass_source_step, scfg_bypass_jump_aligned]
QED
