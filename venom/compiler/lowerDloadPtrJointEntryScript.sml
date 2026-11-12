(* Actual supply-threaded entry control witnesses. *)
Theory lowerDloadPtrJointEntry
Ancestors
  lowerDloadPtrPhi lowerDloadPtrRel o1ContractLowerDload
  lowerDloadPtrStatic o1PassLift o1PassContract venomPassSchedule
  lowerDloadPtrEntry lowerDloadPtrAggregate ptrDiscipline venomWf
  unitTransformDefs irSupply
  contextCodegenRel venomExecSemantics venomExecProofs venomInst lowerDloadDefs list rich_list

Theorem dload_insts_entry_control[local]:
  !xs q ys q'. lower_dload_insts_supply q xs = (ys,q') /\
    phi_prefix_length ys < LENGTH ys ==>
  ?i emitted after.
    phi_prefix_length xs < LENGTH xs /\
    i = EL (phi_prefix_length xs) xs /\
    lower_dload_insts_supply q (TAKE (phi_prefix_length xs) xs) =
      (TAKE (phi_prefix_length xs) xs,q) /\
    lower_dload_inst_supply q i = (emitted,after) /\
    emitted <> [] /\ HD emitted = EL (phi_prefix_length ys) ys
Proof
  Induct >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply q h = ([h],q)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> gvs[phi_prefix_length_def] >>
      `phi_prefix_length outs < LENGTH outs` by decide_tac >>
      first_x_assum drule_all >> strip_tac >>
      qexistsl [`emitted`,`after`] >>
      simp[Once lower_dload_insts_supply_def]) >>
  `out <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  Cases_on `out` >- gvs[] >>
  `h'.inst_opcode <> PHI` by
    (strip_tac >> drule lower_dload_inst_supply_control >> simp[] >> metis_tac[]) >>
  gvs[phi_prefix_length_def] >> simp[lower_dload_insts_supply_def]
QED

Theorem dload_blocks_entry_supply[local]:
  !bs q cs q' lbl b'.
  lower_dload_blocks_supply q bs = (cs,q') /\
  lookup_block lbl cs = SOME b' ==>
  ?bi b u'. bi < LENGTH bs /\ b = EL bi bs /\ b.bb_label = lbl /\
    lookup_block lbl bs = SOME b /\
    lower_dload_block_supply
      (SND (lower_dload_blocks_supply q (TAKE bi bs))) b = (b',u')
Proof
  Induct >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >> strip_tac >>
  `bb'.bb_label = h.bb_label` by
    (gvs[lower_dload_block_supply_def, AllCaseEqs()] >> simp[]) >>
  gvs[lookup_block_def, FIND_thm] >> Cases_on `h.bb_label = lbl` >> gvs[]
  >- (qexists_tac `0` >> simp[lower_dload_blocks_supply_def]) >>
  first_x_assum drule >> simp[lookup_block_def] >>
  disch_then drule >> strip_tac >>
  qexists_tac `SUC bi` >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  Cases_on `lower_dload_blocks_supply s1 (TAKE bi bs)` >> gvs[]
QED

Theorem dload_phis_control[local]:
  !xs s s'. eval_phis s xs = OK s' ==>
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb
Proof
  Induct >> simp[Once eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> gvs[venomStateTheory.update_var_def]
QED

Theorem dload_enters_block_control_match:
  lower_dload_function_supply q f = (g,q') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  enters_block f s s1 /\ enters_block g t t1 /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  active_inst g j t1 ==>
  ?i emitted. dload_control_match q f g s1 t1 i emitted 0 /\ j = HD emitted
Proof
  strip_tac >>
  qpat_x_assum `enters_block g t t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  drule dload_phis_control >> strip_tac >>
  `MEM bb g.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  `t1.vs_current_bb = t.vs_current_bb` by simp[] >>
  `t1.vs_prev_bb = t.vs_prev_bb` by simp[] >>
  `t1.vs_inst_idx = phi_prefix_length bb.bb_instructions` by simp[] >>
  qpat_x_assum `active_inst g j t1` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[]) >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `?gbs. lower_dload_blocks_supply q f.fn_blocks = (g.fn_blocks,gbs)` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all dload_blocks_entry_supply >> strip_tac >>
  drule lower_dload_block_supply_phi_exact >> strip_tac >>
  qpat_x_assum `enters_block f s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule dload_phis_control >> strip_tac >>
  `?aq. lower_dload_insts_supply
      (SND (lower_dload_blocks_supply q (TAKE bi f.fn_blocks)))
      (EL bi f.fn_blocks).bb_instructions = (bb.bb_instructions,aq)` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by metis_tac[] >>
  drule_all dload_insts_entry_control >> strip_tac >>
  qexistsl [`i`,`emitted`] >> simp[] >>
  simp[dload_control_match_def] >>
  qexists_tac `bi` >> simp[] >>
  qexists_tac `after` >>
  gvs[active_inst_def] >> conj_tac
  >- (Cases_on `emitted` >> gvs[]) >> conj_tac
  >- (qexists_tac `EL bi f.fn_blocks` >> simp[EL_MEM]) >>
  qexists_tac `bb` >> Cases_on `emitted` >> gvs[]
QED

Theorem dload_stage_lookup_back:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C'.ctx_functions = SOME g ==>
  ?f q q'. lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn q f /\ lower_dload_function_supply q f = (g,q')
Proof
  strip_tac >>
  `LIST_REL (\f g. ?q q'. ir_supply_covers_fn q f /\
       lower_dload_function_supply q f = (g,q')) C.ctx_functions C'.ctx_functions` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def, LIST_REL_EL_EQN] >> strip_tac >>
     rpt strip_tac >> `n < LENGTH C.ctx_functions` by simp[] >>
     first_x_assum drule >> strip_tac >>
     drule fn_pass_step_input_covers_fn >> strip_tac >>
     gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]) >>
  drule list_rel_lookup_function >>
  impl_tac >- (rpt strip_tac >> gvs[lower_dload_function_supply_def, AllCaseEqs()]) >>
  disch_then (qspec_then `name` mp_tac) >> simp[optionTheory.OPTREL_def] >>
  Cases_on `lookup_function name C.ctx_functions` >> simp[] >> metis_tac[]
QED

Theorem dload_no_phi_entry:
  first_block_no_phi f /\ fn_entry_label f = SOME lbl ==>
  (enters_block f
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t <=>
   t = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  Cases_on `f.fn_blocks` >> simp[fn_entry_label_def, entry_block_def] >> strip_tac >> gvs[] >>
  `phi_prefix_length h.bb_instructions = 0 /\
   (!s. eval_phis s h.bb_instructions = OK s)` by
    (qpat_x_assum `first_block_no_phi f` mp_tac >>
     simp[first_block_no_phi_def] >>
     Cases_on `h.bb_instructions` >>
     simp[phi_prefix_length_def, eval_phis_def]) >>
  simp[enters_block_def, lookup_block_def, FIND_thm] >> metis_tac[]
QED

Theorem dload_actual_joint_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  C'.ctx_entry = SOME name /\ lookup_function name C'.ctx_functions = SOME g /\
  fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst g j t ==>
  ?f q q' i emitted s k.
    C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME f /\
    fn_entry_label f = SOME lbl /\
    enters_block f
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
    frame_reachable vs C [] [] FEMPTY entry_taint f i s /\
    ir_supply_covers_fn q f /\ lower_dload_function_supply q f = (g,q') /\
    dload_control_match q f g s t i emitted 0 /\ j = HD emitted /\
    k < LENGTH C.ctx_functions /\ EL k C.ctx_functions = f /\
    dload_boundary_core lo
      [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
      {v | ~retpc_var f v} [] [] [] FEMPTY FEMPTY entry_taint entry_taint s t [] [] /\
    (!v. lookup_var v s = lookup_var v t) /\
    s.vs_allocas = FEMPTY /\ t.vs_allocas = FEMPTY /\
    ({} = FDOM t.vs_allocas DIFF {id | ?ci. MEM ci (fn_insts f) /\ ci.inst_id = id})
Proof
  strip_tac >> drule_all dload_stage_lookup_back >> strip_tac >>
  `MEM f C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `wf_function f /\ first_block_no_phi f` by
    (gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `fn_entry_label f = SOME lbl` by
    (drule lower_dload_function_supply_labels >>
     gvs[fn_entry_label_def, entry_block_def, fn_labels_def] >>
     Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >> gvs[]) >>
  `f.fn_blocks <> []` by
    (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  `first_block_no_phi g` by
    (drule_all lower_dload_function_supply_first_no_phi >> simp[]) >>
  `t = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    metis_tac[dload_no_phi_entry] >>
  `enters_block f t t` by metis_tac[dload_no_phi_entry] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >> gvs[wf_function_def, fn_labels_def]) >>
  `enters_block g t t` by metis_tac[] >>
  `?i emitted. dload_control_match q f g t t i emitted 0 /\ j = HD emitted` by
    (irule dload_enters_block_control_match >> simp[] >>
     qexistsl [`t`,`t`] >> metis_tac[]) >>
  `C.ctx_entry = SOME name` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >> simp[ctx_pass_stage_def]) >>
  `active_inst f i t` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  `frame_reachable vs C [] [] FEMPTY entry_taint f i t` by
    (irule frame_reachable_entry >> metis_tac[]) >>
  `mem_inv dload_headroom_ok C vs` by gvs[o1_src_inv_def] >>
  `vs.vs_alloca_next < dimword (:256)` by
    (irule dload_active_entry_frontier_bound >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `o1_run_state_ok t` by
    (qpat_x_assum `o1_run_state_ok vs` mp_tac >>
     simp[o1_run_state_ok_def, o1_initial_state_ok_def, code_layout_valid_def]) >>
  `lo <= t.vs_alloca_next` by
    (qpat_x_assum `ptr_discipline lo C vs` mp_tac >> simp[ptr_discipline_def]) >>
  `t.vs_alloca_next < dimword (:256)` by simp[] >>
  `t.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `?k. k < LENGTH C.ctx_functions /\ EL k C.ctx_functions = f` by
    metis_tac[MEM_EL] >>
  qexistsl [`f`,`q`,`q'`,`i`,`emitted`,`t`,`k`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule dload_boundary_initial >> metis_tac[]
QED

(* The original-variable boundary used by the strengthened invariant.  Opaque
   variables are retained for definedness, but excluded from value matching. *)
Theorem dload_actual_joint_entry_tracked:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  C'.ctx_entry = SOME name /\ lookup_function name C'.ctx_functions = SOME g /\
  fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst g j t ==>
  ?f q q' i emitted s k.
    C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME f /\
    frame_reachable vs C [] [] FEMPTY entry_taint f i s /\
    ir_supply_covers_fn q f /\ lower_dload_function_supply q f = (g,q') /\
    dload_control_match q f g s t i emitted 0 /\ j = HD emitted /\
    k < LENGTH C.ctx_functions /\ EL k C.ctx_functions = f /\
    dload_boundary_core lo
      [<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]
      ({v | ?ci. MEM ci (fn_insts f) /\
          (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)}
        DIFF {v | retpc_var f v})
      [] [] [] FEMPTY FEMPTY entry_taint entry_taint s t [] [] /\
    (!v. (?ci. MEM ci (fn_insts f) /\
          (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)) ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    FDOM FEMPTY SUBSET fn_pv P f /\
    (!n b sz. n < LENGTH ([]:(num # num) option list) /\
       EL n [] = SOME (b,sz) ==> n IN P f.fn_name) /\
    s.vs_allocas = FEMPTY /\ t.vs_allocas = FEMPTY /\
    ({} = FDOM t.vs_allocas DIFF {id | ?ci. MEM ci (fn_insts f) /\ ci.inst_id = id}) /\
    (!n. n < LENGTH ([]:call_frame list) ==> F)
Proof
  strip_tac >> drule_all dload_actual_joint_entry >> strip_tac >>
  qexistsl [`f`,`q`,`q'`,`i`,`emitted`,`s`,`k`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (irule dload_boundary_vars_restrict >>
       goal_assum (drule_at Any) >> simp[pred_setTheory.SUBSET_DEF] >> NO_TAC) >>
  simp[NoAsms] >> metis_tac[]
QED
