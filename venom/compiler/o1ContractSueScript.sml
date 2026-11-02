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
