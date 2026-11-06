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
  irSupply unitShapeDefs o1PassContract

Definition make_ssa_pos_def:
  make_ssa_pos fn fn' l k =
    k + (case (lookup_block l fn.fn_blocks, lookup_block l fn'.fn_blocks) of
           (SOME bb, SOME bb') =>
             LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions
         | _ => 0)
End

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
