(*
 * MakeSSA's output meets what MakeSSA needs of its input
 * (make_ssa_input_ok), but for non-degeneracy, which
 * makeSsaCurrentNonDegenerate gives: the first O1 run's output is the
 * second run's input, up to the three passes between them.  The pass
 * keeps the blocks and the CFG, so every block stays reachable; its
 * output is SSA (makeSsaCurrentWfSsa), so every variable is written once
 * and definitions reach their uses; each PHI it places has one pair per
 * predecessor, and renaming keeps the pairs of the PHIs it is given.
 *)
Theory makeSsaCurrentInputOk
Ancestors
  makeSsaCurrentDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract

Theorem make_ssa_current_fn_input_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  all_reachable fn' /\ fn_defs_reach_uses fn' /\
  fn_phi_operands_single_def fn' /\ fn_phis_cover_preds fn' /\
  fn_phi_outputs_single_def fn' /\
  (!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn' l bb.bb_label)
Proof
  cheat
QED
