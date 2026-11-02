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

(* Runs of the expanded function correspond to runs of the original, in
   any context. *)
Theorem sue_expand_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  cheat
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
