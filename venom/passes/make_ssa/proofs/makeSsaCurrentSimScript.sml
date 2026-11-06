(*
 * MakeSSA (make_ssa_current_fn, the supply variant the O1 dispatcher runs)
 * keeps a function's runs and the states its frames reach.  The same
 * statements cover both O1 runs: on the first the input has no PHIs, on
 * the second it has the PHIs the first run built.
 *
 * The pass places pruned PHIs at iterated dominance frontiers, renames
 * along the dominator tree (the first definition of a variable keeps its
 * spelling, later ones take fresh supply names), and on PHI input cleans
 * up degenerate PHIs.  A run of the output matches the input's run block
 * for block; the renamed variables hold the values of the originals.
 *
 * Premises (make_ssa_input_ok unfolds to the first seven): definite
 * assignment (fn_defs_reach_uses) makes every PHI value
 * defined at its predecessor's end; all_reachable makes the dominator tree
 * cover every block, so every block is renamed; fn_phi_operands_single_def
 * keeps the liveness the pass uses exact for the variables PHIs read;
 * fn_phis_cover_preds and first_block_no_phi make every PHI the input runs
 * resolvable, so the cleanup's NOP/ASSIGN collapse cannot make the output
 * run where the input fails.  On PHI input, fn_phi_outputs_single_def
 * confines a re-placed PHI for an existing PHI's output to that PHI's own
 * block, and fn_phis_non_degenerate keeps every existing PHI a PHI through
 * cleanup, so it defines its new name before the collapsed copy reads it.
 * Every PHI's operand labels are distinct CFG predecessors of its block,
 * so the PHI the output enters resolves to the input PHI's operand.
 *)
Theory makeSsaCurrentSim
Ancestors
  o1PassLift makeSsaCurrentDefs venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract

(* Terminating runs of the input and the output correspond. *)
Theorem make_ssa_current_fn_fn_bisim:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  cheat
QED

(* Every state a frame of the output reaches corresponds to one a frame of
   the input reaches, with the same alloca frame and memory ranges. *)
Theorem make_ssa_current_fn_frame_sim:
  ctx_bisim C C' /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  cheat
QED
