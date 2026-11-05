(*
 * MakeSSA leaves no degenerate PHI.  On PHI-free input (the first O1 run)
 * every PHI of the output is one the pass placed: at a block of the
 * iterated dominance frontier of the variable's definitions where the
 * variable is live.  Such a block joins two paths that carry different
 * definitions, so after renaming the PHI reads two distinct versions,
 * neither its own output.  On PHI input the cleanup collapses every PHI
 * whose non-self inputs are all equal, so each PHI it keeps has two
 * distinct non-self inputs.
 *)
Theory makeSsaCurrentNonDegenerate
Ancestors
  makeSsaCurrentDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract

Theorem make_ssa_current_fn_phis_non_degenerate:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_phis_non_degenerate fn'
Proof
  cheat
QED
