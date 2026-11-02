(*
 * MakeSSA (the supply variant the O1 dispatcher runs, make_ssa_current_fn)
 * against the O1 pass contract.  The same statements cover both runs: on
 * the first run the input has no PHIs, on the second it has the PHIs the
 * first run built.
 *
 * The pass places pruned PHIs (where the variable is live) at iterated
 * dominance frontiers, renames along the dominator tree (the first
 * definition of a variable keeps its spelling, later ones take fresh supply
 * names), and on PHI input cleans up degenerate PHIs.  A run of the output
 * matches the input's run block for block; the renamed variables hold the
 * values of the originals.
 *
 * Premises: definite assignment (fn_defs_reach_uses) makes every PHI value
 * defined at its predecessor's end; all_reachable makes the dominator tree
 * cover every block, so every block is renamed; fn_phi_operands_single_def
 * keeps the liveness the pass uses exact for the variables PHIs read.
 *)
Theory o1ContractMakeSsa
Ancestors
  o1PassLift makeSsaCurrentDefs makeSsaCurrentProps venomFnScheduleRunner
  venomWf cfgWf venomInst irSupply unitShapeDefs

Theorem make_ssa_current_fn_fn_bisim:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  cheat
QED

(* Renaming changes no memory operand's value and no INVOKE argument's
   value; inserted PHIs and cleaned-up PHIs touch no memory. *)
Theorem make_ssa_current_fn_frame_sim:
  ctx_bisim C C' /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  cheat
QED
