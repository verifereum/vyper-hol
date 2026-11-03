(*
 * Single-use expansion (the supply variant the O1 dispatcher runs)
 * against the O1 pass contract.
 *
 * The pass only inserts ASSIGNs of fresh variables in front of the
 * instruction that reads them, so every run of the expanded function
 * matches a run of the original one, and vice versa, with the same
 * values and the same state outside the frame's variables.  An inserted
 * ASSIGN of a variable fails only if the variable is undefined; the
 * original instruction may ignore that operand (CALLER [%x]), so the
 * expansion needs every read variable defined when read, which wf_ssa
 * gives (def_dominates_uses).
 *)
Theory o1ContractSue
Ancestors
  o1ContractSueStep o1PassContract
  o1PassLift singleUseExpansionDefs singleUseExpansionSupplyProofs
  venomFnScheduleRunner venomWf venomInst irSupply singleUseExpansionSupplySim

Theorem sue_run_blocks_supply_entry:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  fn_entry_state fn st ==>
  sue_result_rel (set (fn_ir_vars fn)) (run_blocks fuel ctx fn st)
    (run_blocks fuel ctx fn' st)
Proof
  strip_tac >> irule sue_run_blocks_supply_sim >> simp[] >>
  fs[fn_entry_state_def] >>
  `strict_dom_vars_defined fn st` by
    metis_tac[sccpCorrectnessProofsTheory.strict_dom_vars_defined_entry] >>
  simp[fn_reachable_def] >> metis_tac[]
QED

(* Original-frame definedness, independent of any transformed program. *)
Definition sue_frame_defined_def:
  sue_frame_defined fn st <=>
    fn_reachable fn st.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks /\ bb.bb_label = st.vs_current_bb ==>
      sue_boundary_defined fn bb st.vs_inst_idx st /\
      phi_prefix_length bb.bb_instructions <= st.vs_inst_idx)
End

Theorem sue_frame_defined_enter:
  wf_function fn /\ fn_reachable fn st.vs_current_bb /\
  strict_dom_vars_defined fn st /\ enters_block fn st st1 ==>
  sue_frame_defined fn st1
Proof
  rw[contextCodegenRelTheory.enters_block_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM,
              venomExecProofsTheory.lookup_block_label] >>
  `s_phi.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  simp[sue_frame_defined_def] >> rpt strip_tac >>
  rename1 `MEM bb' fn.fn_blocks` >>
  `bb' = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >> metis_tac[sue_boundary_defined_phis]
QED

Theorem sue_frame_defined_next:
  wf_function fn /\ fn_inst_wf fn /\ sue_frame_defined fn st /\
  active_inst fn inst st /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK st' ==>
  sue_frame_defined fn (st' with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  strip_tac >>
  `st'.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  fs[sue_frame_defined_def] >>
  simp[sue_frame_defined_def] >> rpt gen_tac >> strip_tac >>
  fs[contextCodegenRelTheory.active_inst_def] >>
  rename1 `MEM bb' fn.fn_blocks` >>
  `bb' = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >>
  `bb_well_formed bb` by metis_tac[venomExecProofsTheory.wf_function_bb_well_formed] >>
  `inst_wf (EL st.vs_inst_idx bb.bb_instructions)` by
    metis_tac[venomExecProofsTheory.fn_inst_wf_every_bb, listTheory.EVERY_EL] >>
  `sue_boundary_defined fn bb st.vs_inst_idx st /\
   phi_prefix_length bb.bb_instructions <= st.vs_inst_idx` by metis_tac[] >>
  conj_tac >- (irule sue_boundary_defined_step >>
    metis_tac[sue_phi_suffix_nonphi]) >> decide_tac
QED

Theorem sue_frame_defined_block:
  wf_function fn /\ fn_inst_wf fn /\ sue_frame_defined fn st /\
  active_inst fn inst st /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK st' /\ ~st'.vs_halted /\
  enters_block fn st' st1 ==>
  sue_frame_defined fn st1
Proof
  strip_tac >> irule sue_frame_defined_enter >>
  fs[contextCodegenRelTheory.active_inst_def, sue_frame_defined_def] >>
  `bb_well_formed bb` by
    metis_tac[venomExecProofsTheory.wf_function_bb_well_formed] >>
  `EVERY inst_wf bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.fn_inst_wf_every_bb] >>
  `fn_cfg_edge fn st.vs_current_bb st'.vs_current_bb` by
    metis_tac[sue_terminator_cfg_edge] >>
  `FDOM st.vs_vars SUBSET FDOM st'.vs_vars` by
    metis_tac[sue_terminator_domain_mono] >>
  `strict_dom_vars_defined fn st'` by
    (irule sue_boundary_defined_exit >> metis_tac[]) >>
  metis_tac[venomExecProofsTheory.fn_reachable_step]
QED

Theorem sue_frame_reach_defined:
  !ctx fn s0 inst st. frame_reach ctx fn s0 inst st ==>
    active_inst fn inst st /\
    (wf_function fn /\ fn_inst_wf fn /\ fn_entry_state fn s0 ==>
     sue_frame_defined fn st)
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (conj_tac >- simp[] >> strip_tac >>
      irule sue_frame_defined_enter >> simp[] >> qexists_tac `s0` >>
      fs[fn_entry_state_def] >>
      `strict_dom_vars_defined fn s0` by
        metis_tac[sccpCorrectnessProofsTheory.strict_dom_vars_defined_entry] >>
      simp[fn_reachable_def])
  >- (conj_tac >- simp[] >> strip_tac >>
      irule sue_frame_defined_next >> metis_tac[])
  >- (conj_tac >- simp[] >> strip_tac >>
      irule sue_frame_defined_block >> metis_tac[])
QED

Theorem sue_frame_reach_operand_defined:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  fn_entry_state fn s0 /\ frame_reach ctx fn s0 inst st /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  v IN FDOM st.vs_vars
Proof
  strip_tac >> drule sue_frame_reach_defined >> strip_tac >>
  fs[contextCodegenRelTheory.active_inst_def, sue_frame_defined_def] >>
  irule sue_boundary_operand_defined >> metis_tac[]
QED

Definition sue_frame_align_def:
  sue_frame_align C C' fn fn' s0 inst' t <=>
    ?bb bb' bs be segs i j u b.
      frame_reach C fn s0 (EL i bb.bb_instructions) u /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      sue_segments_supply (dfg_build_function fn) bs bb.bb_instructions = (segs,be) /\
      bb' = bb with bb_instructions := FLAT segs /\
      ir_supply_inst_ok bs /\ set (fn_ir_vars fn) SUBSET set bs.irs_used_vars /\
      i < LENGTH bb.bb_instructions /\ u.vs_inst_idx = i /\
      phi_prefix_length bb.bb_instructions <= i /\
      j < LENGTH (EL i segs) /\
      t.vs_inst_idx = sue_segment_offset segs i + j /\
      inst' = EL j (EL i segs) /\ b.vs_inst_idx = 0 /\
      sue_state_rel (set (fn_ir_vars fn)) u b /\
      run_insts 0 C' (TAKE j (BUTLAST (EL i segs))) b = OK (sue_idx0 t)
End

Theorem sue_expanded_active_lookup:
  wf_function fn /\ sue_expand_function_supply supply fn = (fn',supply') /\
  active_inst fn' inst t ==>
  ?bb. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
       t.vs_inst_idx < LENGTH bb.bb_instructions /\
       EL t.vs_inst_idx bb.bb_instructions = inst
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn'.fn_blocks)` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) supply fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def] >>
     drule sue_expand_blocks_supply_labels >>
     fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  fs[contextCodegenRelTheory.active_inst_def] >>
  qexists_tac `bb` >> simp[] >>
  irule venomExecProofsTheory.MEM_lookup_block >> simp[]
QED

Theorem sue_paired_block_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks =
    SOME (bb with bb_instructions := FLAT segs) /\
  ir_supply_inst_ok bs /\
  sue_segments_supply dfg bs bb.bb_instructions = (segs,be) /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN P) bb.bb_instructions /\
  sue_state_rel P s t /\ enters_block fn' t t1 ==>
  ?u. enters_block fn s u /\ sue_state_rel P u t1 /\
      u.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
      t1.vs_inst_idx = sue_segment_offset segs (phi_prefix_length bb.bb_instructions) /\
      u.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb
Proof
  strip_tac >>
  drule sue_segments_supply_flat >> strip_tac >>
  drule_all sue_expand_insts_supply_phis >>
  disch_then (qspec_then `t` strip_assume_tac) >>
  fs[contextCodegenRelTheory.enters_block_def] >> gvs[] >>
  drule_all sue_expanded_phi_entry >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[sue_result_rel_def, stateEquivTheory.lift_result_def] >> strip_tac >>
  gvs[stateEquivTheory.lift_result_def] >>
  drule_all sue_segments_phi_offset >> simp[] >>
  metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb]
QED

Theorem sue_frame_align_enter:
  wf_function fn /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  sue_state_rel (set (fn_ir_vars fn)) s t /\
  enters_block fn' t t1 /\ active_inst fn' inst' t1 /\
  (!u inst. enters_block fn s u /\ active_inst fn inst u ==>
      frame_reach C fn s0 inst u) ==>
  sue_frame_align C C' fn fn' s0 inst' t1
Proof
  strip_tac >>
  `?bt z. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
          eval_phis t bt.bb_instructions = OK z /\
          t1 = z with vs_inst_idx := phi_prefix_length bt.bb_instructions` by
    fs[contextCodegenRelTheory.enters_block_def] >>
  drule_all sue_function_lookup_ready_back >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by fs[sue_state_rel_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN set (fn_ir_vars fn))
    bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> metis_tac[sue_original_operand_covered]) >>
  `?u. enters_block fn s u /\ sue_state_rel (set (fn_ir_vars fn)) u t1 /\
       u.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
       t1.vs_inst_idx = sue_segment_offset segs (phi_prefix_length bb.bb_instructions) /\
       u.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb` by
    (irule sue_paired_block_entry >> simp[] >>
     conj_tac >- metis_tac[] >> qexists_tac `fn'` >> fs[]) >>
  `?bb1. lookup_block t1.vs_current_bb fn'.fn_blocks = SOME bb1 /\
         t1.vs_inst_idx < LENGTH bb1.bb_instructions /\
         EL t1.vs_inst_idx bb1.bb_instructions = inst'` by
    metis_tac[sue_expanded_active_lookup] >>
  `bb1 = bt` by metis_tac[optionTheory.SOME_11] >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (drule sue_segments_supply_length >> strip_tac >>
     `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
       simp[venomExecProofsTheory.phi_prefix_length_le] >>
     spose_not_then assume_tac >>
     `phi_prefix_length bb.bb_instructions = LENGTH segs` by decide_tac >>
     `t1.vs_inst_idx = LENGTH (FLAT segs)` by metis_tac[sue_segment_offset_end] >>
     `bt.bb_instructions = FLAT segs` by simp[] >> metis_tac[prim_recTheory.LESS_REFL]) >>
  `0 < LENGTH (EL (phi_prefix_length bb.bb_instructions) segs)` by
    (drule sue_segments_supply_length >> strip_tac >>
     drule sue_segments_supply_nonempty >> simp[listTheory.EVERY_EL] >> strip_tac >>
     `EL (phi_prefix_length bb.bb_instructions) segs <> []` by metis_tac[] >>
     Cases_on `EL (phi_prefix_length bb.bb_instructions) segs` >> fs[]) >>
  `EL (sue_segment_offset segs (phi_prefix_length bb.bb_instructions)) (FLAT segs) =
   EL 0 (EL (phi_prefix_length bb.bb_instructions) segs)` by
    (qspec_then `segs` (qspec_then `phi_prefix_length bb.bb_instructions`
       (qspec_then `0` mp_tac)) sue_segment_offset_el >>
     drule sue_segments_supply_length >> simp[]) >>
  `active_inst fn (EL u.vs_inst_idx bb.bb_instructions) u` by
    (simp[contextCodegenRelTheory.active_inst_def] >> qexists_tac `bb` >>
     simp[] >> metis_tac[venomExecProofsTheory.lookup_block_label]) >>
  `frame_reach C fn s0 (EL u.vs_inst_idx bb.bb_instructions) u` by metis_tac[] >>
  pure_rewrite_tac[sue_frame_align_def] >>
  qexistsl [`bb`, `bt`, `si`, `sj`, `segs`, `u.vs_inst_idx`, `0`, `u`, `sue_idx0 t1`] >>
  simp[sue_idx0_def, sue_state_rel_def, stateFrameTheory.execution_frame_def,
       analysisSimDefsTheory.run_insts_def] >> gvs[]
QED

Theorem sue_frame_align_initial:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  fn_entry_state fn s0 /\ enters_block fn' s0 t /\ active_inst fn' inst' t ==>
  sue_frame_align C C' fn fn' s0 inst' t
Proof
  strip_tac >> irule sue_frame_align_enter >> simp[] >>
  conj_tac >- (qexistsl [`supply`, `supply'`] >> simp[]) >>
  qexistsl [`s0`, `s0`] >> simp[sue_state_rel_def] >>
  metis_tac[frame_reach_rules]
QED

Theorem sue_expand_inst_supply_final_ok_back:
  ctx_bisim C C' /\ ir_supply_inst_ok supply /\
  sue_expand_inst_supply dfg supply inst = (segment,supply') /\
  P SUBSET set supply.irs_used_vars /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN P) /\
  inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  sue_state_rel P s b /\
  run_insts 0 C' (BUTLAST segment) b = OK (sue_idx0 t) /\
  step_inst fuel C' (LAST segment) t = OK v ==>
  ?fuel0 u. step_inst fuel0 C inst s = OK u /\ sue_state_rel P u v
Proof
  strip_tac >>
  `sue_result_rel P (step_inst fuel C' inst s) (OK v)` by
    metis_tac[sue_expand_inst_supply_final_step] >>
  `?u. step_inst fuel C' inst s = OK u /\ sue_state_rel P u v` by
    (Cases_on `step_inst fuel C' inst s` >>
     gvs[sue_result_rel_def, stateEquivTheory.lift_result_def]) >>
  drule (cj 2 ctx_bisim_step_inst) >>
  disch_then (qspecl_then [`fuel`, `inst`, `s`] mp_tac) >>
  simp[passSimulationDefsTheory.terminates_def] >> strip_tac >>
  Cases_on `step_inst fuel' C inst s` >>
  gvs[step_result_rel_def, frame_result_rel_def] >> metis_tac[]
QED

Theorem sue_segment_final_ok_back:
  ctx_bisim C C' /\ fn_inst_wf fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  sue_segments_supply (dfg_build_function fn) bs bb.bb_instructions = (segs,be) /\
  ir_supply_inst_ok bs /\ set (fn_ir_vars fn) SUBSET set bs.irs_used_vars /\
  i < LENGTH bb.bb_instructions /\
  sue_state_rel (set (fn_ir_vars fn)) u b /\
  run_insts 0 C' (BUTLAST (EL i segs)) b = OK (sue_idx0 t) /\
  step_inst fuel C' (LAST (EL i segs)) t = OK v ==>
  (LAST (EL i segs)).inst_opcode = (EL i bb.bb_instructions).inst_opcode /\
  ?fuel0 w. step_inst fuel0 C (EL i bb.bb_instructions) u = OK w /\
            sue_state_rel (set (fn_ir_vars fn)) w v
Proof
  strip_tac >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[listTheory.EL_MEM] >>
  `inst_wf (EL i bb.bb_instructions)` by
    metis_tac[venomExecProofsTheory.fn_inst_wf_every_bb, listTheory.EVERY_MEM] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (`!bbs. MEM bb bbs ==> MEM (EL i bb.bb_instructions) (fn_insts_blocks bbs)` by
       (Induct >> simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]) >>
     simp[venomInstTheory.fn_insts_def]) >>
  `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` by
    (qpat_x_assum `EVERY (\inst. inst.inst_opcode <> ALLOCA) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `~is_alloca_op (EL i bb.bb_instructions).inst_opcode` by
    (Cases_on `(EL i bb.bb_instructions).inst_opcode` >>
     fs[venomInstTheory.is_alloca_op_def]) >>
  conj_tac
  >- (drule_all sue_expand_inst_supply_segment >> strip_tac >> simp[]) >>
  irule sue_expand_inst_supply_final_ok_back >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[sue_original_operand_covered]
QED

(* The explicit witnesses are the elimination interface of sue_frame_align.
   A copy advances only the target cursor, never the source reachability. *)
Theorem sue_frame_align_copy_advance:
  wf_function fn /\ sue_expand_function_supply supply fn = (fn',supply') /\
  frame_reach C fn s0 (EL i bb.bb_instructions) u /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  sue_segments_supply (dfg_build_function fn) bs bb.bb_instructions = (segs,be) /\
  bb' = bb with bb_instructions := FLAT segs /\
  ir_supply_inst_ok bs /\ set (fn_ir_vars fn) SUBSET set bs.irs_used_vars /\
  i < LENGTH bb.bb_instructions /\ u.vs_inst_idx = i /\
  phi_prefix_length bb.bb_instructions <= i /\
  j < LENGTH (BUTLAST (EL i segs)) /\
  t.vs_inst_idx = sue_segment_offset segs i + j /\
  inst' = EL j (EL i segs) /\ b.vs_inst_idx = 0 /\
  sue_state_rel (set (fn_ir_vars fn)) u b /\
  run_insts 0 C' (TAKE j (BUTLAST (EL i segs))) b = OK (sue_idx0 t) /\
  step_inst fuel C' inst' t = OK v /\
  active_inst fn' next (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  sue_frame_align C C' fn fn' s0 next (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  `BUTLAST (EL i segs) = assigns` by
    simp[rich_listTheory.FRONT_APPEND_NOT_NIL] >>
  `j < LENGTH assigns /\ SUC j < LENGTH (EL i segs)` by fs[] >>
  `EL j (EL i segs) = EL j assigns` by
    simp[listTheory.EL_APPEND_EQN] >>
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    fs[listTheory.EVERY_MEM] >>
  `run_insts 0 C' (TAKE (SUC j) (BUTLAST (EL i segs))) b =
    OK (sue_idx0 (v with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule sue_assign_prefix_advance >>
     goal_assum (drule_at Any) >> fs[] >> metis_tac[]) >>
  `inst'.inst_opcode = ASSIGN` by fs[listTheory.EVERY_EL] >>
  `v.vs_current_bb = t.vs_current_bb` by
    (drule venomInstProofsTheory.step_preserves_control_flow >>
     simp[venomInstTheory.is_terminator_def]) >>
  drule_all sue_expanded_active_lookup >> strip_tac >>
  `bb'' = bb'` by gvs[] >>
  `i < LENGTH segs` by metis_tac[sue_segments_supply_length] >>
  `next = EL (SUC j) (EL i segs)` by
    (drule_all sue_segment_offset_el >> strip_tac >>
     gvs[arithmeticTheory.ADD_CLAUSES]) >>
  pure_rewrite_tac[sue_frame_align_def] >>
  qexistsl [`bb`, `bb'`, `bs`, `be`, `segs`, `i`, `SUC j`, `u`, `b`] >>
  simp[] >> decide_tac
QED

Theorem sue_frame_align_next:
  ctx_bisim C C' /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  sue_frame_align C C' fn fn' s0 inst' t /\
  ~is_terminator inst'.inst_opcode /\ step_inst fuel C' inst' t = OK v /\
  active_inst fn' next (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  sue_frame_align C C' fn fn' s0 next (v with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> qpat_x_assum `sue_frame_align _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[sue_frame_align_def]) >>
  Cases_on `j < LENGTH (BUTLAST (EL i segs))`
  >- (irule sue_frame_align_copy_advance >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  `EL i segs <> []` by
    (drule sue_segments_supply_nonempty >>
     drule sue_segments_supply_length >> simp[listTheory.EVERY_EL] >> metis_tac[]) >>
  `j = LENGTH (BUTLAST (EL i segs)) /\ EL j (EL i segs) = LAST (EL i segs)` by
    (Cases_on `EL i segs` >> fs[rich_listTheory.LENGTH_BUTLAST,
       listTheory.LAST_EL] >> `j = LENGTH t'` by decide_tac >> simp[]) >>
  `run_insts 0 C' (BUTLAST (EL i segs)) b = OK (sue_idx0 t)` by fs[] >>
  `step_inst fuel C' (LAST (EL i segs)) t = OK v` by metis_tac[] >>
  drule_all sue_segment_final_ok_back >> strip_tac >>
  `~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `w.vs_current_bb = u.vs_current_bb /\ v.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
  `LENGTH segs = LENGTH bb.bb_instructions` by metis_tac[sue_segments_supply_length] >>
  `SUC t.vs_inst_idx = sue_segment_offset segs (SUC i)` by
    (qspec_then `segs` (qspec_then `i` mp_tac) sue_segment_offset_suc >>
     Cases_on `EL i segs` >> fs[rich_listTheory.LENGTH_BUTLAST] >> decide_tac) >>
  drule_all sue_expanded_active_lookup >> strip_tac >>
  `bb'' = bb'` by gvs[] >>
  `SUC i < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >> `SUC i = LENGTH segs` by decide_tac >>
     `sue_segment_offset segs (SUC i) = LENGTH (FLAT segs)` by
       metis_tac[sue_segment_offset_end] >> gvs[]) >>
  `EL (SUC i) segs <> []` by
    (drule sue_segments_supply_nonempty >> simp[listTheory.EVERY_EL] >> metis_tac[]) >>
  `next = EL 0 (EL (SUC i) segs)` by
    (qspec_then `segs` (qspec_then `SUC i` (qspec_then `0` mp_tac)) sue_segment_offset_el >>
     Cases_on `EL (SUC i) segs` >> gvs[]) >>
  `active_inst fn (EL (SUC i) bb.bb_instructions)
     (w with vs_inst_idx := SUC u.vs_inst_idx)` by
    (simp[contextCodegenRelTheory.active_inst_def] >> qexists_tac `bb` >>
     simp[] >> metis_tac[venomExecProofsTheory.lookup_block_label,
                            venomExecProofsTheory.lookup_block_MEM]) >>
  `frame_reach C fn s0 (EL (SUC i) bb.bb_instructions)
     (w with vs_inst_idx := SUC u.vs_inst_idx)` by metis_tac[frame_reach_rules] >>
  pure_rewrite_tac[sue_frame_align_def] >>
  qexistsl [`bb`, `bb'`, `bs`, `be`, `segs`, `SUC i`, `0`,
    `w with vs_inst_idx := SUC u.vs_inst_idx`, `sue_idx0 v`] >>
  simp[sue_state_rel_def, sue_idx0_def, stateFrameTheory.execution_frame_def,
       analysisSimDefsTheory.run_insts_def] >>
  conj_tac >- (Cases_on `EL (SUC i) segs` >> fs[]) >>
  fs[sue_state_rel_def, stateFrameTheory.execution_frame_def]
QED

Theorem sue_frame_align_block:
  ctx_bisim C C' /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  sue_frame_align C C' fn fn' s0 inst' t /\
  is_terminator inst'.inst_opcode /\ step_inst fuel C' inst' t = OK v /\
  ~v.vs_halted /\ enters_block fn' v t1 /\ active_inst fn' next t1 ==>
  sue_frame_align C C' fn fn' s0 next t1
Proof
  strip_tac >> qpat_x_assum `sue_frame_align _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[sue_frame_align_def]) >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  `BUTLAST (EL i segs) = assigns` by
    simp[rich_listTheory.FRONT_APPEND_NOT_NIL] >>
  `~(j < LENGTH assigns)` by
    (strip_tac >>
     `inst'.inst_opcode = ASSIGN` by
       fs[listTheory.EL_APPEND_EQN, listTheory.EVERY_EL] >>
     fs[venomInstTheory.is_terminator_def]) >>
  `j = LENGTH assigns` by fs[] >>
  `inst' = LAST (EL i segs) /\ j = LENGTH (BUTLAST (EL i segs))` by
    fs[listTheory.EL_APPEND_EQN] >>
  `run_insts 0 C' (BUTLAST (EL i segs)) b = OK (sue_idx0 t) /\
   step_inst fuel C' (LAST (EL i segs)) t = OK v` by fs[] >>
  drule_all sue_segment_final_ok_back >> strip_tac >>
  `is_terminator (EL i bb.bb_instructions).inst_opcode /\ ~w.vs_halted` by
    fs[sue_state_rel_def, stateFrameTheory.execution_frame_def] >>
  irule sue_frame_align_enter >> simp[] >>
  conj_tac >- (qexistsl [`supply`, `supply'`] >> simp[]) >>
  qexistsl [`w`, `v`] >> simp[] >> rpt gen_tac >> strip_tac >>
  irule (cj 3 frame_reach_rules) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem sue_frame_align_state:
  sue_frame_align C C' fn fn' s0 inst' t ==>
  ?inst u. frame_reach C fn s0 inst u /\
           sue_state_rel (set (fn_ir_vars fn)) u t
Proof
  rw[sue_frame_align_def] >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  qexistsl [`EL u.vs_inst_idx bb.bb_instructions`, `u`] >> simp[] >>
  irule sue_assign_prefix_normalized_rel >> goal_assum (drule_at Any) >>
  simp[] >> fs[rich_listTheory.FRONT_APPEND_NOT_NIL,
               listTheory.EVERY_MEM, listTheory.MEM_FLAT,
               listTheory.MEM_MAP, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

Theorem sue_terminating_result_frame:
  terminates r /\ (!st. r <> OK st) /\ sue_result_rel P r r' ==>
  frame_result_rel r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[passSimulationDefsTheory.terminates_def, sue_result_rel_def,
       stateEquivTheory.lift_result_def, frame_result_rel_def, sue_term_rel_def] >>
  metis_tac[]
QED

Theorem sue_run_result_frame:
  terminates (run_blocks fuel ctx fn s) /\
  sue_result_rel P (run_blocks fuel ctx fn s) r' ==>
  frame_result_rel (run_blocks fuel ctx fn s) r'
Proof
  strip_tac >> irule sue_terminating_result_frame >>
  simp[sue_run_blocks_never_ok] >> qexists_tac `P` >> simp[]
QED

Theorem sue_assign_observations:
  a.inst_opcode = ASSIGN /\ sue_state_rel P s t ==>
  mem_corr inst s a t /\ call_corr inst s a t
Proof
  strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
   t.vs_initial_fmp = s.vs_initial_fmp` by
    (fs[sue_state_rel_def] >>
     drule stateFrameTheory.execution_frame_projection >>
     simp[stateFrameTheory.execution_frame_def]) >>
  simp[mem_corr_def, call_corr_def, unitMemInvTheory.inst_mem_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem sue_eval_operands_related[local]:
  !xs ys. LIST_REL (\op newop. eval_operand newop t = eval_operand op s) xs ys ==>
    eval_operands ys t = eval_operands xs s
Proof
  Induct >> Cases_on `ys` >>
  simp[venomStateTheory.eval_operands_def] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem sue_rewritten_call_observation:
  inst_wf inst /\ execution_frame s = execution_frame t /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops /\
  (!i. i < LENGTH inst.inst_operands ==>
    !lbl. EL i inst.inst_operands = Label lbl ==> EL i ops = Label lbl) ==>
  call_corr inst s (inst with inst_operands := ops) t
Proof
  strip_tac >>
  `execution_frame t = execution_frame s` by metis_tac[] >>
  simp[call_corr_def] >> strip_tac >>
  gvs[inst_wf_def] >>
  `newop = Label lbl` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[venomExecSemanticsTheory.decode_invoke_def] >>
  irule sue_eval_operands_related >> simp[]
QED

Theorem sue_rewritten_read_ranges_plain[local]:
  inst.inst_opcode <> LOG /\ inst.inst_opcode <> DRET /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops ==>
  source_memory_read_ranges (inst with inst_operands := ops) t =
  source_memory_read_ranges inst s
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [MLOAD; ILOAD; MCOPY; RETURN; REVERT; SHA3;
              CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (qpat_x_assum `MEM _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
      simp[contextCodegenRelTheory.source_memory_read_ranges_def] >>
      rpt (qmatch_asmsub_rename_tac `LIST_REL _ xs ys` >>
        Cases_on `xs` >> Cases_on `ys` >>
        gvs[contextCodegenRelTheory.memory_range_of_operands_def])) >>
  (* every other opcode reads no memory, whatever its operands *)
  `!vs (i:instruction). i.inst_opcode = inst.inst_opcode ==>
                        source_memory_read_ranges i vs = []` by
    (simp[contextCodegenRelTheory.source_memory_read_ranges_def] >>
     Cases_on `inst.inst_opcode` >> fs[]) >>
  simp[]
QED

Theorem sue_rewritten_write_ranges_plain[local]:
  inst.inst_opcode <> DRET /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops ==>
  source_memory_write_ranges (inst with inst_operands := ops) t =
  source_memory_write_ranges inst s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[codegenRelTheory.source_memory_write_ranges_def] >>
  rpt (qmatch_asmsub_rename_tac `LIST_REL _ xs ys` >>
    Cases_on `xs` >> Cases_on `ys` >>
    gvs[codegenRelTheory.fixed_source_write_range_def,
        codegenRelTheory.sized_source_write_range_def])
QED

Theorem sue_rewritten_dret_ranges[local]:
  inst.inst_opcode = DRET /\ s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
  parse_dret_shape (inst with inst_operands := ops) = parse_dret_shape inst /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops ==>
  inst_mem_ranges (inst with inst_operands := ops) t = inst_mem_ranges inst s
Proof
  strip_tac >> drule sue_eval_operands_related >> strip_tac >>
  simp[unitMemInvTheory.inst_mem_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       contextCodegenRelTheory.dret_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem sue_rewritten_log_ranges[local]:
  inst_wf inst /\ inst.inst_opcode = LOG /\
  HD ops = HD inst.inst_operands /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops ==>
  source_memory_read_ranges (inst with inst_operands := ops) t =
  source_memory_read_ranges inst s
Proof
  strip_tac >> gvs[inst_wf_def] >>
  rename1 `LIST_REL _ rest tail` >>
  `LENGTH tail = LENGTH rest` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  `LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
     (REVERSE rest) (REVERSE tail)` by
    metis_tac[listTheory.LIST_REL_REVERSE] >>
  `eval_operands (DROP 2 (REVERSE tail)) t =
   eval_operands (DROP 2 (REVERSE rest)) s` by
    (irule sue_eval_operands_related >>
     irule rich_listTheory.LIST_REL_DROP >> simp[]) >>
  `eval_operand (EL 0 (REVERSE tail)) t =
   eval_operand (EL 0 (REVERSE rest)) s /\
   eval_operand (EL 1 (REVERSE tail)) t =
   eval_operand (EL 1 (REVERSE rest)) s` by
    (qpat_x_assum `LIST_REL _ (REVERSE _) (REVERSE _)` mp_tac >>
     pure_rewrite_tac[listTheory.LIST_REL_EL_EQN, listTheory.LENGTH_REVERSE] >>
     strip_tac >> conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >>
         BETA_TAC >> disch_then irule >> decide_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >>
     BETA_TAC >> disch_then irule >> decide_tac) >>
  qpat_x_assum `eval_operand (EL 0 _) _ = _`
    (assume_tac o REWRITE_RULE[listTheory.EL]) >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def]
QED

Theorem sue_rewritten_mem_observation:
  inst_wf inst /\ execution_frame s = execution_frame t /\
  LIST_REL (\op newop. eval_operand newop t = eval_operand op s)
    inst.inst_operands ops /\
  (inst.inst_opcode = LOG ==> HD ops = HD inst.inst_operands) /\
  (inst.inst_opcode = DRET ==>
    parse_dret_shape (inst with inst_operands := ops) = parse_dret_shape inst) ==>
  mem_corr inst s (inst with inst_operands := ops) t
Proof
  strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
   t.vs_initial_fmp = s.vs_initial_fmp /\
   s.vs_call_entry_fmp = t.vs_call_entry_fmp` by
    (fs[stateFrameTheory.execution_frame_def,
        venomStateTheory.venom_state_component_equality]) >>
  simp[mem_corr_def] >> disj2_tac >>
  Cases_on `inst.inst_opcode = DRET`
  >- (irule sue_rewritten_dret_ranges >> simp[]) >>
  simp[unitMemInvTheory.inst_mem_ranges_def] >>
  `source_memory_write_ranges (inst with inst_operands := ops) t =
   source_memory_write_ranges inst s` by
    (irule sue_rewritten_write_ranges_plain >> simp[]) >>
  simp[] >>
  Cases_on `inst.inst_opcode = LOG`
  >- (irule sue_rewritten_log_ranges >> simp[]) >>
  irule sue_rewritten_read_ranges_plain >> simp[]
QED

Theorem sue_segment_observations:
  inst_wf inst /\ ir_supply_inst_ok si /\
  sue_expand_inst_supply dfg si inst = (segment,sj) /\
  P SUBSET set si.irs_used_vars /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) /\
  sue_state_rel P u b /\ j < LENGTH segment /\
  run_insts 0 ctx (TAKE j (BUTLAST segment)) b = OK (sue_idx0 t) ==>
  mem_corr inst u (EL j segment) t /\ call_corr inst u (EL j segment) t
Proof
  strip_tac >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  `sue_state_rel P u t` by
    (irule sue_assign_prefix_normalized_rel >> goal_assum (drule_at Any) >>
     simp[] >> fs[rich_listTheory.FRONT_APPEND_NOT_NIL,
       listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP,
       pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  Cases_on `j < LENGTH assigns`
  >- (`(EL j segment).inst_opcode = ASSIGN` by
        (gvs[listTheory.EL_APPEND_EQN, listTheory.EVERY_EL]) >>
      irule sue_assign_observations >> simp[] >> qexists_tac `P` >> simp[]) >>
  `j = LENGTH assigns` by fs[] >>
  gvs[rich_listTheory.FRONT_APPEND_NOT_NIL, listTheory.EL_APPEND_EQN] >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- (drule sue_expand_inst_supply_skip >> strip_tac >>
      `assigns ++ [inst with inst_operands := new_ops] = [inst]` by
        metis_tac[pairTheory.PAIR_EQ] >>
      `LAST (assigns ++ [inst with inst_operands := new_ops]) = inst` by
        metis_tac[listTheory.LAST_DEF] >>
      `inst with inst_operands := new_ops = inst` by
        fs[listTheory.LAST_APPEND_CONS] >>
      `LIST_REL (\op newop. eval_operand newop t = eval_operand op u)
         inst.inst_operands inst.inst_operands` by
        (simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
         irule sue_state_rel_eval_operand >> qexists_tac `P` >>
         simp[] >> metis_tac[listTheory.MEM_EL]) >>
      simp[] >> conj_tac
      >- (`mem_corr inst u (inst with inst_operands := inst.inst_operands) t`
            suffices_by simp[] >>
          irule sue_rewritten_mem_observation >> fs[sue_state_rel_def]) >>
      `call_corr inst u (inst with inst_operands := inst.inst_operands) t`
        suffices_by simp[] >>
      irule sue_rewritten_call_observation >> fs[sue_state_rel_def]) >>
  Cases_on `sue_expand_ops_supply dfg inst si inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  `r0 = new_ops` by
    (qpat_x_assum `inst with inst_operands := _ = _` mp_tac >>
     simp[venomInstTheory.instruction_component_equality]) >>
  gvs[] >>
  drule_all sue_expand_ops_supply_normalized_eval >> strip_tac >>
  drule sue_expand_ops_supply_structure >> strip_tac >>
  conj_tac
  >- (irule sue_rewritten_mem_observation >> fs[sue_state_rel_def]) >>
  irule sue_rewritten_call_observation >> fs[sue_state_rel_def]
QED

Theorem sue_frame_align_observations:
  fn_inst_wf fn /\ sue_frame_align C C' fn fn' s0 inst' t ==>
  ?inst u. frame_reach C fn s0 inst u /\
           mem_corr inst u inst' t /\ call_corr inst u inst' t
Proof
  rw[sue_frame_align_def] >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `inst_wf (EL u.vs_inst_idx bb.bb_instructions)` by
    metis_tac[venomExecProofsTheory.fn_inst_wf_every_bb, listTheory.EVERY_EL] >>
  `!v. MEM (Var v) (EL u.vs_inst_idx bb.bb_instructions).inst_operands ==>
       v IN set (fn_ir_vars fn)` by
    metis_tac[sue_original_operand_covered, listTheory.MEM_EL] >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  qexistsl [`EL u.vs_inst_idx bb.bb_instructions`, `u`] >> simp[] >>
  irule sue_segment_observations >> simp[] >>
  qexists_tac `set (fn_ir_vars fn)` >> simp[] >>
  qexistsl [`b`, `C'`] >> simp[] >>
  metis_tac[]
QED

Theorem sue_frame_reach_align:
  !C' fn' s0 inst' t. frame_reach C' fn' s0 inst' t ==>
  !C fn supply supply'.
    ctx_bisim C C' /\ wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
    ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
    sue_expand_function_supply supply fn = (fn',supply') /\ fn_entry_state fn s0 ==>
    sue_frame_align C C' fn fn' s0 inst' t
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (rpt gen_tac >> strip_tac >> irule sue_frame_align_initial >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> irule sue_frame_align_next >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> irule sue_frame_align_block >> metis_tac[])
QED

(* Runs of the expanded function correspond to runs of the original, in
   any context. *)
Theorem sue_expand_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  strip_tac >> drule sue_expand_function_supply_identity >> strip_tac >>
  simp[fn_bisim_def] >> rpt gen_tac >> strip_tac >>
  `!fuel. sue_result_rel (set (fn_ir_vars fn))
    (run_blocks fuel ctx fn s'') (run_blocks fuel ctx fn' s'')` by
    (gen_tac >> irule sue_run_blocks_supply_entry >> metis_tac[]) >>
  conj_tac >> gen_tac >> strip_tac
  >- (qexists_tac `fuel` >> irule sue_run_result_frame >> metis_tac[]) >>
  qexists_tac `fuel'` >> irule sue_run_result_frame >>
  reverse conj_tac >- (qexists_tac `set (fn_ir_vars fn)` >> simp[]) >>
  first_x_assum (qspec_then `fuel'` mp_tac) >>
  Cases_on `run_blocks fuel' ctx fn s''` >>
  Cases_on `run_blocks fuel' ctx fn' s''` >>
  gvs[sue_result_rel_def, stateEquivTheory.lift_result_def,
      passSimulationDefsTheory.terminates_def]
QED

(* Every state a frame of the expanded function reaches corresponds to one
   the original reaches: an inserted ASSIGN touches no memory, and every
   original instruction keeps its memory ranges and INVOKE arguments. *)
Theorem sue_expand_function_supply_frame_sim:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  sue_expand_function_supply s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  strip_tac >> rw[frame_sim_def] >>
  drule_all sue_frame_reach_align >> strip_tac >>
  irule sue_frame_align_observations >> metis_tac[]
QED

(* ===== The stage contract (run 6) ===== *)

(* The expanded function does not depend on which instruction ids the
   supply records as used: fresh ids come from irs_next_inst alone.  So a
   stage step, which says nothing of ir_supply_inst_ok, can be replayed
   from a supply that has it. *)
Theorem sue_expand_function_supply_used_inst_ids:
  FST (sue_expand_function_supply (s with irs_used_inst_ids := ids) fn) =
  FST (sue_expand_function_supply s fn)
Proof
  simp[sue_expand_function_supply_def] >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  drule sue_expand_blocks_supply_used_inst_ids >>
  disch_then (qspec_then `ids` strip_assume_tac) >>
  simp[]
QED

(* Row 6 (o1_ssa_inv: wf_ssa, no ALLOCA) to row 7. *)
Theorem sue_stage_walk:
  o1_run_contract rpolicy 6
Proof
  cheat
QED

Theorem o1_contract_sue:
  o1_step_contract_at 6 rpolicy (CFP_Simple VP_SingleUseExpansion) /\
  o1_run_contract rpolicy 6
Proof
  simp[sue_step_contract, sue_stage_walk]
QED
