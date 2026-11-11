(*
 * MakeSSA's output runs in lockstep with its input: every output frame
 * path is matched step for step by an input path, renaming variables
 * point by point, with a target-only step only for an ASSIGN copy or a
 * NOP (a PHI the cleanup collapsed).  Instruction k of an input block
 * sits at make_ssa_pos in the output block of the same label: MakeSSA
 * only adds PHIs at the head of a block.  The pointer, taint,
 * source-shape and frame_sim_rf rows transport their path ghosts through
 * it.
 *)
Theory makeSsaCurrentLockstep
Ancestors
  o1FrameLockstep o1PassLift makeSsaDefs venomWf cfgWf venomInst
  irSupply unitShapeDefs o1PassContract venomState stateFrame venomExecSemantics
  venomExecProps venomExecProofs contextCodegenRel list rich_list
  makeSsaCurrentCutInv makeSsaCurrentWfSsa o1MakeSsaFormats
  makeSsaCurrentLockstepShape analysisSimProofsBase rangeAnalysisProofs venomInstProofs venomInstProofs1

Definition make_ssa_pos_def:
  make_ssa_pos fn fn' l k =
    k + (case (lookup_block l fn.fn_blocks, lookup_block l fn'.fn_blocks) of
           (SOME bb, SOME bb') =>
             LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions
         | _ => 0)
End

Theorem op_rename_mono:
  (!x' x. FLOOKUP sg1 x' = SOME x ==> FLOOKUP sg0 x' = SOME x) /\
  op_rename sg1 op op' ==> op_rename sg0 op op'
Proof
  Cases_on `op'` >> simp[op_rename_def] >> metis_tac[]
QED

Theorem phis_rename_ok_mono:
  (!x' x. FLOOKUP sg1 x' = SOME x ==> FLOOKUP sg0 x' = SOME x) /\
  phis_rename_ok prev sg1 xs ys sg2 ==>
  phis_rename_ok prev sg0 xs ys sg2
Proof
  rw[phis_rename_ok_def] >>
  first_x_assum drule >>
  Cases_on `phi_eff prev x xs` >> Cases_on `phi_eff prev x' ys` >>
  simp[optionTheory.OPTREL_def] >> metis_tac[op_rename_mono]
QED

Theorem out_rename_ok_empty_restrict:
  out_rename_ok sg [] outs' sg1 ==>
  !x' x. FLOOKUP sg1 x' = SOME x ==> FLOOKUP sg x' = SOME x
Proof
  simp[out_rename_ok_def] >> metis_tac[]
QED

Theorem state_rel_copy:
  state_rel sg st st' /\ copy_rename_ok sg inst' sg1 /\
  (inst'.inst_opcode = ASSIGN \/ inst'.inst_opcode = NOP) /\
  step_inst fuel C' inst' st' = OK t' ==>
  state_rel sg1 st t'
Proof
  strip_tac >>
  ` (inst'.inst_opcode = NOP /\ t' = st') \/
    (?x' op v. inst'.inst_opcode = ASSIGN /\ inst'.inst_operands = [op] /\
      inst'.inst_outputs = [x'] /\ eval_operand op st' = SOME v /\
      t' = update_var x' v st') ` by metis_tac[step_inst_copy] >>
  gvs[state_rel_def, vars_rel_def, copy_rename_ok_def,
      update_var_def, lookup_var_def, execution_frame_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  first_x_assum drule >> simp[]
QED

Theorem state_rel_inst_idx[simp]:
  (state_rel sg (st with vs_inst_idx := i) st' <=> state_rel sg st st') /\
  (state_rel sg st (st' with vs_inst_idx := j) <=> state_rel sg st st')
Proof
  simp[state_rel_def, execution_frame_def]
QED

Theorem current_cut_inv_inst_idx[simp]:
  (current_cut_inv fn A renamed H events l k (st with vs_inst_idx := i) st' <=>
   current_cut_inv fn A renamed H events l k st st') /\
  (current_cut_inv fn A renamed H events l k st (st' with vs_inst_idx := j) <=>
   current_cut_inv fn A renamed H events l k st st')
Proof
  simp[current_cut_inv_def, lookup_var_def]
QED

Theorem lockstep_terminator_boundary:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst st = OK t /\ ~t.vs_halted ==>
  SUC i = LENGTH bb.bb_instructions /\ inst.inst_outputs = [] /\
  t.vs_prev_bb = SOME st.vs_current_bb /\
  MEM t.vs_current_bb (bb_succs bb)
Proof
  strip_tac >>
  `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[bb_well_formed_def] >>
  `SUC i = LENGTH bb.bb_instructions` by decide_tac >>
  `inst_wf inst` by metis_tac[EVERY_EL] >>
  `inst.inst_outputs = []` by metis_tac[terminator_no_outputs] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `step_inst_base inst st = OK t` by gvs[step_inst_non_invoke] >>
  `t.vs_prev_bb = SOME st.vs_current_bb` by
    metis_tac[step_inst_base_term_prev_bb] >>
  `inst = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL]) >>
  Cases_on `bb.bb_instructions` >>
  gvs[bb_succs_def, MEM_nub] >>
  metis_tac[step_inst_base_term_succs]
QED

Theorem lockstep_active_terminator_edge:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn inst st /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst st = OK t /\
  ~t.vs_halted ==>
  inst.inst_outputs = [] /\ t.vs_prev_bb = SOME st.vs_current_bb /\
  fn_cfg_edge fn st.vs_current_bb t.vs_current_bb
Proof
  strip_tac >> fs[active_inst_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `inst = EL st.vs_inst_idx bb.bb_instructions` by simp[] >>
  drule_all lockstep_terminator_boundary >> strip_tac >>
  qpat_x_assum `inst = EL _ _` kall_tac >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem make_ssa_pos_suc[simp]:
  make_ssa_pos fn fn' l (SUC k) = SUC (make_ssa_pos fn fn' l k)
Proof
  simp[make_ssa_pos_def]
QED

Theorem make_ssa_pos_prefix:
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l fn'.fn_blocks = SOME new /\
  LENGTH new.bb_instructions = LENGTH pre + LENGTH old.bb_instructions ==>
  make_ssa_pos fn fn' l i = LENGTH pre + i
Proof
  simp[make_ssa_pos_def]
QED

Theorem make_ssa_lockstep_phi_context:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  entry_block fn = SOME eb /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?renamed A H events.
    current_wf_phi_context s fn renamed s' A H events /\
    fn' = fn with fn_blocks :=
      simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed
Proof
  strip_tac >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  drule_all current_wf_named_structural_certificate >> strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[current_wf_precleanup_certificate_stages] >> strip_tac >>
  qexistsl_tac [`renamed`, `A`, `H`, `events`] >> simp[] >>
  irule current_wf_phi_context_intro >> fs[make_ssa_input_ok_def] >>
  metis_tac[]
QED

Theorem current_phi_context_annotation:
  current_wf_phi_context s fn renamed s' A H events /\
  lookup_block l fn.fn_blocks = SOME old ==>
  ?pre. A l = current_block_annotations old pre
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_insertion_lookup >> metis_tac[]
QED

Theorem current_phi_context_entry_annotation:
  current_wf_phi_context s fn renamed s' A H events /\
  lookup_block l fn.fn_blocks = SOME old /\
  fn_entry_label fn = SOME old.bb_label ==>
  A l = current_block_annotations old []
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  `pre = []` suffices_by metis_tac[] >>
  Cases_on `pre` >- simp[] >>
  fs[EVERY_MEM] >>
  `current_actual_inserted fn w old.bb_label` by
    (first_x_assum (qspec_then `w` mp_tac) >>
     disch_then (irule o iffRL) >> qexists_tac `h` >>
     simp[build_phi_inst_supply_def]) >>
  `wf_function fn /\ all_reachable fn /\ first_block_no_preds fn` by
    fs[current_wf_phi_context_def] >>
  metis_tac[current_wf_inserted_nonentry]
QED

Theorem enters_block_no_phi:
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions /\
  st.vs_inst_idx = 0 ==>
  (enters_block fn st post <=> post = st)
Proof
  strip_tac >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def]) >>
  drule phi_prefix_length_zero_eval_phis_ok >>
  disch_then (qspec_then `st` assume_tac) >>
  simp[enters_block_def]
QED

Theorem make_ssa_lockstep_entry_states:
  make_ssa_current_fn s fn = (fn',s') /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  fn_entry_state fn st /\ enters_block fn' st post' ==>
  enters_block fn st st /\ post' = st
Proof
  strip_tac >>
  drule_all make_ssa_current_fn_first_block_no_phi >> strip_tac >>
  drule o1MakeSsaCfgTheory.make_ssa_current_fn_entry_label >> strip_tac >>
  `fn_entry_state fn' st` by gvs[fn_entry_state_def] >>
  `?bb. lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (gvs[fn_entry_state_def, fn_entry_label_def, entry_block_def,
         first_block_no_phi_def, AllCaseEqs()] >>
     Cases_on `fn.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  `?bb'. lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb' /\
    EVERY (\i. i.inst_opcode <> PHI) bb'.bb_instructions` by
    (gvs[fn_entry_state_def, fn_entry_label_def, entry_block_def,
         first_block_no_phi_def, AllCaseEqs()] >>
     Cases_on `fn'.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  `st.vs_inst_idx = 0` by fs[fn_entry_state_def] >>
  metis_tac[enters_block_no_phi]
QED

Theorem current_phi_context_entry_cut:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\ entry_block fn = SOME eb /\ fn_entry_state fn st ==>
  ?bb'. lookup_block eb.bb_label fn.fn_blocks = SOME eb /\
    lookup_block eb.bb_label fn'.fn_blocks = SOME bb' /\
    A eb.bb_label = current_block_annotations eb [] /\
    LENGTH bb'.bb_instructions = LENGTH eb.bb_instructions /\
    LENGTH (collect_phis eb.bb_instructions) = 0 /\
    make_ssa_pos fn fn' eb.bb_label 0 = 0 /\
    current_cut_inv fn A renamed H events eb.bb_label 0 st st /\
    current_cut_sg fn A renamed H events eb.bb_label 0 = FEMPTY
Proof
  strip_tac >>
  `wf_function fn /\ first_block_no_phi fn` by
    fs[current_wf_phi_context_def] >>
  `MEM eb fn.fn_blocks /\ fn_entry_label fn = SOME eb.bb_label` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def, fn_entry_label_def]) >>
  `lookup_block eb.bb_label fn.fn_blocks = SOME eb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `A eb.bb_label = current_block_annotations eb []` by
    metis_tac[current_phi_context_entry_annotation] >>
  `EVERY (\i. i.inst_opcode <> PHI) eb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def, first_block_no_phi_def]) >>
  `LENGTH (collect_phis eb.bb_instructions) = 0` by
    (Cases_on `eb.bb_instructions` >> gvs[livenessDefsTheory.collect_phis_def]) >>
  `0 < LENGTH eb.bb_instructions` by
    (fs[wf_function_def, EVERY_MEM] >>
     `bb_well_formed eb` by metis_tac[] >>
     fs[bb_well_formed_def] >> Cases_on `eb.bb_instructions` >> gvs[]) >>
  `st.vs_current_bb = eb.bb_label` by fs[fn_entry_state_def] >>
  drule_all current_cut_inv_entry >> strip_tac >>
  `LENGTH (collect_phis eb.bb_instructions) <= 0` by decide_tac >>
  drule_all current_cut_inv_ordinary_step >> strip_tac >>
  qexists_tac `bb'` >> gvs[make_ssa_pos_def]
QED

Definition current_cleanup_tail_def:
  current_cleanup_tail fn A renamed H events l i xs end q sgs st st' <=>
    q <= end /\
    sgs end = current_cut_sg fn A renamed H events l i /\
    state_rel (sgs q) st st' /\
    (!v. current_demand fn v l i ==> IS_SOME (lookup_var v st)) /\
    (!k. q <= k /\ k < end ==>
      ((EL k xs).inst_opcode = ASSIGN \/
       (EL k xs).inst_opcode = NOP /\ (EL k xs).inst_operands = []) /\
      copy_rename_ok (sgs k) (EL k xs) (sgs (SUC k)))
End

Definition current_lockstep_rel_def:
  current_lockstep_rel fn fn' A renamed H events p (inst,st) sg (inst',st') <=>
    active_inst fn inst st /\ active_inst fn' inst' st' /\
    st'.vs_current_bb = st.vs_current_bb /\
    ?old bb' pre.
      lookup_block st.vs_current_bb fn.fn_blocks = SOME old /\
      lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb' /\
      A st.vs_current_bb = current_block_annotations old pre /\
      LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
      if p then
        LENGTH (collect_phis old.bb_instructions) <= st.vs_inst_idx /\
        st'.vs_inst_idx = LENGTH pre + st.vs_inst_idx /\
        sg = current_cut_sg fn A renamed H events st.vs_current_bb st.vs_inst_idx /\
        current_cut_inv fn A renamed H events st.vs_current_bb st.vs_inst_idx st st'
      else
        st.vs_inst_idx = LENGTH (collect_phis old.bb_instructions) /\
        st'.vs_inst_idx < LENGTH pre + st.vs_inst_idx /\
        ?sgs. sg = sgs st'.vs_inst_idx /\
          current_cleanup_tail fn A renamed H events st.vs_current_bb st.vs_inst_idx
            bb'.bb_instructions (LENGTH pre + st.vs_inst_idx) st'.vs_inst_idx sgs st st'
End

Theorem current_cleanup_tail_endpoint:
  current_cleanup_tail fn A renamed H events l i xs end end sgs st st' ==>
  current_cut_inv fn A renamed H events l i st st'
Proof
  rw[current_cleanup_tail_def, current_cut_inv_def] >> gvs[]
QED

Theorem current_cleanup_tail_step:
  current_cleanup_tail fn A renamed H events l i xs end q sgs st st' /\
  q < end /\ step_inst fuel C' (EL q xs) st' = OK t' ==>
  current_cleanup_tail fn A renamed H events l i xs end (SUC q) sgs st t' /\
  copy_rename_ok (sgs q) (EL q xs) (sgs (SUC q))
Proof
  strip_tac >> fs[current_cleanup_tail_def] >>
  `((EL q xs).inst_opcode = ASSIGN \/
    (EL q xs).inst_opcode = NOP /\ (EL q xs).inst_operands = []) /\
    copy_rename_ok (sgs q) (EL q xs) (sgs (SUC q))` by simp[] >>
  `state_rel (sgs (SUC q)) st t'` by metis_tac[state_rel_copy] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem current_lockstep_paired_intro:
  active_inst fn inst st /\ active_inst fn' inst' st' /\
  st'.vs_current_bb = st.vs_current_bb /\
  lookup_block st.vs_current_bb fn.fn_blocks = SOME old /\
  lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb' /\
  A st.vs_current_bb = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  LENGTH (collect_phis old.bb_instructions) <= st.vs_inst_idx /\
  st'.vs_inst_idx = LENGTH pre + st.vs_inst_idx /\
  current_cut_inv fn A renamed H events st.vs_current_bb st.vs_inst_idx st st' /\
  sg = current_cut_sg fn A renamed H events st.vs_current_bb st.vs_inst_idx ==>
  current_lockstep_rel fn fn' A renamed H events T (inst,st) sg (inst',st')
Proof
  rw[current_lockstep_rel_def] >> qexists_tac `pre` >> simp[]
QED

Theorem current_lockstep_cleanup_intro:
  active_inst fn inst st /\ active_inst fn' inst' st' /\
  st'.vs_current_bb = st.vs_current_bb /\
  lookup_block st.vs_current_bb fn.fn_blocks = SOME old /\
  lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb' /\
  A st.vs_current_bb = current_block_annotations old pre /\
  LENGTH bb'.bb_instructions = LENGTH pre + LENGTH old.bb_instructions /\
  st.vs_inst_idx = LENGTH (collect_phis old.bb_instructions) /\
  current_cleanup_tail fn A renamed H events st.vs_current_bb st.vs_inst_idx
    bb'.bb_instructions (LENGTH pre + st.vs_inst_idx) st'.vs_inst_idx sgs st st' /\
  p = (st'.vs_inst_idx = LENGTH pre + st.vs_inst_idx) /\
  sg = sgs st'.vs_inst_idx ==>
  current_lockstep_rel fn fn' A renamed H events p (inst,st) sg (inst',st')
Proof
  strip_tac >> qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `sg = _` SUBST_ALL_TAC >> Cases_on `st'.vs_inst_idx = LENGTH pre + st.vs_inst_idx`
  >- (fs[] >> drule current_cleanup_tail_endpoint >> strip_tac >>
      fs[current_cleanup_tail_def] >>
      rw[current_lockstep_rel_def] >> qexists_tac `pre` >>
      gvs[current_cut_inv_def]) >>
  rw[current_lockstep_rel_def] >> qexists_tac `pre` >> simp[] >>
  conj_tac >- (fs[current_cleanup_tail_def] >> decide_tac) >>
  qexists_tac `sgs` >> gvs[]
QED

Theorem active_inst_at_lookup:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb ==>
  (active_inst fn inst st <=> st.vs_inst_idx < LENGTH bb.bb_instructions /\
    inst = EL st.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> eq_tac
  >- (rw[active_inst_def] >>
      `lookup_block st.vs_current_bb fn.fn_blocks = SOME bb'` by
        (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  strip_tac >> simp[active_inst_def] >> qexists_tac `bb` >>
  metis_tac[lookup_block_MEM, venomExecProofsTheory.lookup_block_label]
QED

Theorem current_phi_context_output_distinct:
  current_wf_phi_context s fn renamed s' A H events ==>
  ALL_DISTINCT (MAP (\b. b.bb_label)
    (simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed))
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\ wf_function fn` by
    fs[current_wf_phi_context_def] >>
  drule current_wf_precleanup_labels >> strip_tac >>
  fs[wf_function_def, fn_labels_def]
QED

Theorem current_lockstep_rel_boundary:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\
  current_lockstep_rel fn fn' A renamed H events p (inst,st) sg (inst',st') ==>
  active_inst fn inst st /\ active_inst fn' inst' st' /\ state_rel sg st st' /\
  (p ==> inst_pair sg inst inst' /\
    st'.vs_inst_idx = make_ssa_pos fn fn' st.vs_current_bb st.vs_inst_idx) /\
  (~p ==> inst'.inst_opcode = ASSIGN \/
    inst'.inst_opcode = NOP /\ inst'.inst_operands = [])
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[current_wf_phi_context_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (drule current_phi_context_output_distinct >> simp[]) >>
  Cases_on `p`
  >- (fs[current_lockstep_rel_def] >>
      `st.vs_inst_idx < LENGTH old.bb_instructions /\
       inst = EL st.vs_inst_idx old.bb_instructions` by
        metis_tac[active_inst_at_lookup] >>
      `inst' = EL (LENGTH pre + st.vs_inst_idx) bb'.bb_instructions` by
        metis_tac[active_inst_at_lookup] >>
      `st.vs_current_bb = st.vs_current_bb` by simp[] >>
      drule_all current_cut_inv_ordinary_step >> strip_tac >>
      gvs[current_cut_inv_def, make_ssa_pos_def]) >>
  fs[current_lockstep_rel_def, current_cleanup_tail_def] >>
  `inst' = EL st'.vs_inst_idx bb'.bb_instructions` by
    metis_tac[active_inst_at_lookup] >>
  gvs[] >> first_x_assum (qspec_then `st'.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem current_cleanup_tail_inst_idx[simp]:
  (current_cleanup_tail fn A renamed H events l i xs end q sgs
     (st with vs_inst_idx := n) st' <=>
   current_cleanup_tail fn A renamed H events l i xs end q sgs st st') /\
  (current_cleanup_tail fn A renamed H events l i xs end q sgs
     st (st' with vs_inst_idx := n) <=>
   current_cleanup_tail fn A renamed H events l i xs end q sgs st st')
Proof
  simp[current_cleanup_tail_def, lookup_var_def]
QED

Theorem current_lockstep_unpaired_step:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  current_lockstep_rel fn fn' A renamed H events F (inst,st) sg (inst',st') /\
  step_inst fuel C' inst' st' = OK t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC st'.vs_inst_idx) ==>
  ?p sg'. current_lockstep_rel fn fn' A renamed H events p (inst,st) sg'
    (j',t' with vs_inst_idx := SUC st'.vs_inst_idx) /\ copy_rename_ok sg inst' sg'
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (drule current_phi_context_output_distinct >> simp[]) >>
  qpat_x_assum `current_lockstep_rel _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[current_lockstep_rel_def]) >>
  `inst' = EL st'.vs_inst_idx bb'.bb_instructions` by
    metis_tac[active_inst_at_lookup] >>
  `copy_rename_ok (sgs st'.vs_inst_idx)
      (EL st'.vs_inst_idx bb'.bb_instructions) (sgs (SUC st'.vs_inst_idx))` by
    (fs[current_cleanup_tail_def] >> simp[]) >>
  `t'.vs_current_bb = st'.vs_current_bb` by
    (`inst'.inst_opcode = ASSIGN \/ inst'.inst_opcode = NOP` by
       (fs[current_cleanup_tail_def] >>
        first_x_assum (qspec_then `st'.vs_inst_idx` mp_tac) >> simp[] >> metis_tac[]) >>
     `t' = st' \/ ?x v. t' = update_var x v st'` by
       metis_tac[step_inst_copy] >> gvs[update_var_def]) >>
  `current_cleanup_tail fn A renamed H events st.vs_current_bb st.vs_inst_idx
    bb'.bb_instructions (LENGTH pre + st.vs_inst_idx)
    (SUC st'.vs_inst_idx) sgs st t'` by
    metis_tac[current_cleanup_tail_step] >>
  qexistsl_tac [`SUC st'.vs_inst_idx = LENGTH pre + st.vs_inst_idx`,
    `sgs (SUC st'.vs_inst_idx)`] >> conj_tac
  >- (irule current_lockstep_cleanup_intro >> simp[] >>
      qexistsl_tac [`pre`, `sgs`] >> gvs[]) >>
  gvs[]
QED

Theorem current_lockstep_entry:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\ make_ssa_current_fn s fn = (fn',s') /\
  fn_entry_state fn st /\ enters_block fn' st post' /\ active_inst fn' inst' post' ==>
  ?p inst post sg. enters_block fn st post /\
    current_lockstep_rel fn fn' A renamed H events p (inst,post) sg (inst',post')
Proof
  strip_tac >>
  `wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn` by
    fs[current_wf_phi_context_def] >>
  drule_all make_ssa_lockstep_entry_states >> strip_tac >>
  qpat_x_assum `post' = st` SUBST_ALL_TAC >>
  `?eb. entry_block fn = SOME eb` by
    (fs[fn_entry_state_def, fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  drule_all current_phi_context_entry_cut >> strip_tac >>
  `st.vs_current_bb = eb.bb_label /\ st.vs_inst_idx = 0` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (drule current_phi_context_output_distinct >> simp[]) >>
  `0 < LENGTH eb.bb_instructions` by metis_tac[active_inst_at_lookup] >>
  `active_inst fn (EL 0 eb.bb_instructions) st` by
    (irule (iffRL active_inst_at_lookup) >>
     conj_tac >- fs[wf_function_def, fn_labels_def] >>
     qexists_tac `eb` >> simp[]) >>
  qexistsl_tac [`T`, `EL 0 eb.bb_instructions`, `st`, `FEMPTY`] >> simp[] >>
  `FEMPTY = current_cut_sg fn A renamed H events st.vs_current_bb st.vs_inst_idx` by gvs[] >>
  pop_assum SUBST1_TAC >> irule current_lockstep_paired_intro >> simp[] >>
  gvs[]
QED

Theorem current_lockstep_block_entry:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  fn_cfg_edge fn pred h /\ lookup_block pred fn.fn_blocks = SOME old_p /\
  current_cut_inv fn A renamed H events pred (LENGTH old_p.bb_instructions) t t' /\
  t.vs_prev_bb = SOME pred /\ t.vs_current_bb = h /\
  (!x' x. FLOOKUP (current_cut_sg fn A renamed H events pred
      (LENGTH old_p.bb_instructions)) x' = SOME x ==> FLOOKUP incoming x' = SOME x) /\
  enters_block fn' t' post' /\ active_inst fn' j' post' ==>
  ?p j post sg. enters_block fn t post /\
    current_lockstep_rel fn fn' A renamed H events p (j,post) sg (j',post') /\
    phis_rename_ok t.vs_prev_bb incoming (block_insts fn t.vs_current_bb)
      (block_insts fn' t.vs_current_bb) sg
Proof
  strip_tac >>
  drule_all current_cut_inv_block_entry_prefix >> strip_tac >>
  `?post. enters_block fn t post /\
    post.vs_inst_idx = LENGTH (collect_phis old_h.bb_instructions) /\
    state_rel (sgs (phi_prefix_length bb'.bb_instructions)) post post' /\
    (!v. current_demand fn v h (LENGTH (collect_phis old_h.bb_instructions)) ==>
      IS_SOME (lookup_var v post))` by metis_tac[] >>
  `t'.vs_current_bb = h` by fs[current_cut_inv_def, state_rel_def] >>
  `post.vs_current_bb = h /\ post'.vs_current_bb = h /\
    post'.vs_inst_idx = phi_prefix_length bb'.bb_instructions` by
    (fs[enters_block_def] >>
     metis_tac[eval_phis_preserves_current_bb]) >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  `bb_well_formed old_h` by metis_tac[wf_function_def, lookup_block_MEM] >>
  `!xs. LENGTH (collect_phis xs) = phi_prefix_length xs` by
    (Induct >> simp[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
     qx_gen_tac `ins` >> Cases_on `ins.inst_opcode = PHI` >> simp[]) >>
  `LENGTH (collect_phis old_h.bb_instructions) < LENGTH old_h.bb_instructions` by
    (simp[] >> spose_not_then assume_tac >>
     `phi_prefix_length old_h.bb_instructions = LENGTH old_h.bb_instructions` by
       metis_tac[phi_prefix_length_le, arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQUAL_ANTISYM] >>
     fs[bb_well_formed_def] >>
     `LENGTH old_h.bb_instructions <> 0` by
       (Cases_on `old_h.bb_instructions` >> fs[]) >>
     `is_terminator (EL (PRE (LENGTH old_h.bb_instructions)) old_h.bb_instructions).inst_opcode` by
       metis_tac[LAST_EL] >>
     `(EL (PRE (LENGTH old_h.bb_instructions)) old_h.bb_instructions).inst_opcode = PHI` by
       (irule phi_prefix_length_el_phi >> simp[]) >>
     gvs[is_terminator_def]) >>
  `active_inst fn (EL post.vs_inst_idx old_h.bb_instructions) post` by
    (irule (iffRL active_inst_at_lookup) >>
     conj_tac >- fs[wf_function_def, fn_labels_def] >>
     qexists_tac `old_h` >> simp[] >> metis_tac[]) >>
  `current_cleanup_tail fn A renamed H events h post.vs_inst_idx bb'.bb_instructions
      (LENGTH pre + post.vs_inst_idx) post'.vs_inst_idx sgs post post'` by
    (simp[current_cleanup_tail_def] >> metis_tac[]) >>
  qexistsl_tac [`post'.vs_inst_idx = LENGTH pre + post.vs_inst_idx`,
    `EL post.vs_inst_idx old_h.bb_instructions`, `post`, `sgs post'.vs_inst_idx`] >>
  simp[] >> conj_tac
  >- (irule current_lockstep_cleanup_intro >> gvs[] >>
      qexistsl_tac [`pre`, `sgs`] >> simp[]) >>
  irule phis_rename_ok_mono >> goal_assum (drule_at Any) >> gvs[]
QED

Theorem current_lockstep_paired_steps:
  current_wf_phi_context supply fn renamed supply' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\
  current_lockstep_rel fn fn' A renamed H events T (inst,st) sg (inst',st') ==>
  (!fuel t'. inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' st' = OK t' ==>
    ?t. step_inst fuel C inst st = OK t /\
      current_cut_inv fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx) t t' /\
      out_rename_ok sg inst.inst_outputs inst'.inst_outputs
        (current_cut_sg fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx))) /\
  (!fuel v e'. inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' st' = IntRet v e' ==>
    ?e. step_inst fuel C inst st = IntRet v e /\ execution_frame e' = execution_frame e) /\
  (!fuel h'. inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' st' = Halt h' ==>
    ?h. step_inst fuel C inst st = Halt h /\ execution_frame h' = execution_frame h) /\
  (!ret e e' t'. inst'.inst_opcode = INVOKE /\ execution_frame e' = execution_frame e /\
    bind_outputs inst'.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state st' e')) = SOME t' ==>
    ?t. bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state st e)) = SOME t /\
      current_cut_inv fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx) t t' /\
      out_rename_ok sg inst.inst_outputs inst'.inst_outputs
        (current_cut_sg fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx)))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[current_wf_phi_context_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (drule current_phi_context_output_distinct >> simp[]) >>
  qpat_x_assum `current_lockstep_rel _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[current_lockstep_rel_def]) >>
  `st.vs_inst_idx < LENGTH old.bb_instructions /\
    inst = EL st.vs_inst_idx old.bb_instructions` by
    metis_tac[active_inst_at_lookup] >>
  `inst' = EL (LENGTH pre + st.vs_inst_idx) bb'.bb_instructions` by
    metis_tac[active_inst_at_lookup] >>
  `st.vs_current_bb = st.vs_current_bb` by simp[] >>
  drule_all current_cut_inv_ordinary_step >> strip_tac >> gvs[] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem current_lockstep_paired_successor:
  current_wf_phi_context supply fn renamed supply' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  current_lockstep_rel fn fn' A renamed H events T (inst,st) sg (inst',st') /\
  t.vs_current_bb = st.vs_current_bb /\ t'.vs_current_bb = st.vs_current_bb /\
  current_cut_inv fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx) t t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC st'.vs_inst_idx) ==>
  ?j. current_lockstep_rel fn fn' A renamed H events T
    (j,t with vs_inst_idx := SUC st.vs_inst_idx)
    (current_cut_sg fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx))
    (j',t' with vs_inst_idx := SUC st'.vs_inst_idx)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[current_wf_phi_context_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (drule current_phi_context_output_distinct >> simp[]) >>
  qpat_x_assum `current_lockstep_rel _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[current_lockstep_rel_def]) >>
  `SUC st.vs_inst_idx < LENGTH old.bb_instructions` by
    (`SUC st'.vs_inst_idx < LENGTH bb'.bb_instructions` by
      (qpat_x_assum `active_inst fn' j' _` mp_tac >>
       simp[active_inst_def] >> rpt strip_tac >>
       `lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb` by
         (irule MEM_lookup_block >> simp[]) >> gvs[]) >> decide_tac) >>
  `active_inst fn (EL (SUC st.vs_inst_idx) old.bb_instructions)
    (t with vs_inst_idx := SUC st.vs_inst_idx)` by
    (irule (iffRL active_inst_at_lookup) >> simp[] >>
     qexists_tac `old` >> simp[]) >>
  qexists_tac `EL (SUC st.vs_inst_idx) old.bb_instructions` >>
  irule current_lockstep_paired_intro >> simp[] >>
  qexistsl_tac [`bb'`, `pre`] >> gvs[]
QED

Theorem current_lockstep_paired_ok:
  current_wf_phi_context supply fn renamed supply' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\
  current_lockstep_rel fn fn' A renamed H events T (inst,st) sg (inst',st') /\
  inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' st' = OK t' ==>
  ?t. step_inst fuel C inst st = OK t /\ execution_frame t' = execution_frame t /\
    (~is_terminator inst'.inst_opcode ==>
      !j'. active_inst fn' j' (t' with vs_inst_idx := SUC st'.vs_inst_idx) ==>
      ?p j sg1. current_lockstep_rel fn fn' A renamed H events p
        (j,t with vs_inst_idx := SUC st.vs_inst_idx) sg1
        (j',t' with vs_inst_idx := SUC st'.vs_inst_idx) /\
        out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg1) /\
    (is_terminator inst'.inst_opcode ==>
      t'.vs_current_bb = t.vs_current_bb /\ t'.vs_prev_bb = t.vs_prev_bb /\
      !post' j'. ~t'.vs_halted /\ enters_block fn' t' post' /\ active_inst fn' j' post' ==>
      ?p j post sg1. enters_block fn t post /\
        current_lockstep_rel fn fn' A renamed H events p (j,post) sg1 (j',post') /\
        phis_rename_ok t.vs_prev_bb sg (block_insts fn t.vs_current_bb)
          (block_insts fn' t.vs_current_bb) sg1)
Proof
  strip_tac >>
  drule_all current_lockstep_rel_boundary >> strip_tac >>
  `inst.inst_opcode = inst'.inst_opcode` by fs[inst_pair_def] >>
  drule_all current_lockstep_paired_steps >> strip_tac >>
  `?t. step_inst fuel C inst st = OK t /\
    current_cut_inv fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx) t t' /\
    out_rename_ok sg inst.inst_outputs inst'.inst_outputs
      (current_cut_sg fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx))` by
    metis_tac[] >>
  `execution_frame t' = execution_frame t /\
    t'.vs_current_bb = t.vs_current_bb /\ t'.vs_prev_bb = t.vs_prev_bb /\
    (t'.vs_halted = t.vs_halted)` by fs[current_cut_inv_def, state_rel_def] >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (rpt strip_tac >>
      `t.vs_current_bb = st.vs_current_bb /\ t'.vs_current_bb = st.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      drule_all current_lockstep_paired_successor >> strip_tac >>
      qexistsl_tac [`T`, `j`, `current_cut_sg fn A renamed H events st.vs_current_bb
        (SUC st.vs_inst_idx)`] >> simp[]) >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  `is_terminator inst.inst_opcode /\ ~t.vs_halted` by metis_tac[] >>
  `wf_function fn /\ fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  drule_all lockstep_active_terminator_edge >> strip_tac >>
  qpat_x_assum `current_lockstep_rel _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[current_lockstep_rel_def]) >>
  `bb_well_formed old /\ EVERY inst_wf old.bb_instructions` by
    (fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `st.vs_inst_idx < LENGTH old.bb_instructions /\
    inst = EL st.vs_inst_idx old.bb_instructions` by
    (irule (iffLR active_inst_at_lookup) >>
     fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  drule_all lockstep_terminator_boundary >> strip_tac >>
  irule current_lockstep_block_entry >> simp[] >>
  conj_tac >- metis_tac[] >> qexists_tac `t'` >> gvs[] >>
  metis_tac[out_rename_ok_empty_restrict]
QED

Theorem current_lockstep_invoke_return:
  current_wf_phi_context supply fn renamed supply' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\
  current_lockstep_rel fn fn' A renamed H events T (inst,st) sg (inst',st') /\
  inst'.inst_opcode = INVOKE /\ execution_frame e' = execution_frame e /\
  bind_outputs inst'.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state st' e')) = SOME t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC st'.vs_inst_idx) ==>
  ?p j t sg1.
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state st e)) = SOME t /\
    current_lockstep_rel fn fn' A renamed H events p
      (j,t with vs_inst_idx := SUC st.vs_inst_idx) sg1
      (j',t' with vs_inst_idx := SUC st'.vs_inst_idx) /\
    out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg1
Proof
  strip_tac >>
  drule_all current_lockstep_paired_steps >> strip_tac >>
  `?t. bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state st e)) = SOME t /\
    current_cut_inv fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx) t t' /\
    out_rename_ok sg inst.inst_outputs inst'.inst_outputs
      (current_cut_sg fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx))` by metis_tac[] >>
  `!outs vals state post. bind_outputs outs vals state = SOME post ==>
    post.vs_current_bb = state.vs_current_bb` by
    (rpt strip_tac >> irule bind_outputs_preserves >>
     simp[update_var_def] >> metis_tac[]) >>
  `t.vs_current_bb = st.vs_current_bb` by
    (`t.vs_current_bb = (adopt_return_fmp ret (merge_callee_state st e)).vs_current_bb` by
      metis_tac[] >> Cases_on `ret.iret_adopt_fmp` >>
      fs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `t'.vs_current_bb = st.vs_current_bb` by
    (fs[current_cut_inv_def, state_rel_def]) >>
  drule_all current_lockstep_paired_successor >> strip_tac >>
  qexistsl_tac [`T`, `j`, `t`,
    `current_cut_sg fn A renamed H events st.vs_current_bb (SUC st.vs_inst_idx)`] >>
  simp[]
QED

Theorem current_lockstep_sim:
  current_wf_phi_context s fn renamed s' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  ctx_bisim C C' /\ make_ssa_current_fn s fn = (fn',s') ==>
  lockstep_sim L C C' fn fn' (make_ssa_pos fn fn')
    (current_lockstep_rel fn fn' A renamed H events)
Proof
  strip_tac >> rewrite_tac[lockstep_sim_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all current_lockstep_rel_boundary >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule current_lockstep_entry >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule current_lockstep_unpaired_step >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule current_lockstep_paired_ok >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all (cj 2 current_lockstep_paired_steps) >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all (cj 3 current_lockstep_paired_steps) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule current_lockstep_invoke_return >> metis_tac[]
QED

Theorem make_ssa_current_fn_frame_lockstep:
  ctx_bisim C C' /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_lockstep L C C' fn fn' (make_ssa_pos fn fn')
Proof
  strip_tac >>
  `?eb. entry_block fn = SOME eb` by
    (Cases_on `fn.fn_blocks` >>
     fs[wf_function_def, fn_has_entry_def, entry_block_def]) >>
  drule_all make_ssa_lockstep_phi_context >> strip_tac >>
  rewrite_tac[frame_lockstep_def] >> conj_tac >- simp[] >>
  qexists_tac `current_lockstep_rel fn fn' A renamed H events` >>
  irule current_lockstep_sim >> metis_tac[]
QED
