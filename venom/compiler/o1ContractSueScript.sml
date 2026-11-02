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
  strip_tac >> Cases_on `inst.inst_opcode` >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def] >>
  rpt (qmatch_asmsub_rename_tac `LIST_REL _ xs ys` >>
    Cases_on `xs` >> Cases_on `ys` >>
    gvs[contextCodegenRelTheory.memory_range_of_operands_def])
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
  frame_sim C C' fn fn'
Proof
  cheat
QED
