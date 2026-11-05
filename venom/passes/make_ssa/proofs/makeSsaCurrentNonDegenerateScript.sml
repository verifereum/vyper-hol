(*
 * MakeSSA's first O1 run leaves no degenerate PHI.  Its input has no PHI,
 * so every PHI of the output is one the pass placed: at a block of the
 * iterated dominance frontier of the variable's definitions where the
 * variable is live.  Such a block joins two paths that carry different
 * definitions, so after renaming the PHI reads two distinct versions,
 * neither its own output.  The second run's premises (fn_phis_non_degenerate
 * among them) are carried from here to its input by the O1 stage rows.
 *)
Theory makeSsaCurrentNonDegenerate
Ancestors
  makeSsaCurrentDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract

Theorem make_ssa_current_fn_phis_non_degenerate:
  EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn) /\
  fn_defs_reach_uses fn /\ all_reachable fn /\ fn_inst_wf fn /\
  wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_phis_non_degenerate fn'
Proof
  cheat
QED
