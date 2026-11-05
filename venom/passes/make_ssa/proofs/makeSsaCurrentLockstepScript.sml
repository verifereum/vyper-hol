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
  o1FrameLockstep o1PassLift makeSsaCurrentDefs venomWf cfgWf venomInst
  irSupply unitShapeDefs o1PassContract venomState stateFrame venomExecSemantics
  venomExecProps venomExecProofs contextCodegenRel list rich_list
  makeSsaCurrentCutInv

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

Theorem make_ssa_current_fn_frame_lockstep:
  ctx_bisim C C' /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_lockstep L C C' fn fn' (make_ssa_pos fn fn')
Proof
  cheat
QED
