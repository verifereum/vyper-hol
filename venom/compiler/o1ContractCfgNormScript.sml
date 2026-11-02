(*
 * CFG normalization (the supply variant the O1 dispatcher runs) against
 * the O1 pass contract.
 *
 * The pass splits each critical edge p -> t with a fresh block that
 * forwards the PHI values t reads along that edge into fresh variables and
 * jumps to t; t's PHIs then name the split block and the forwarded
 * variables.  A run of the output takes one extra block per split edge
 * and otherwise matches the input's run, so the two correspond with
 * different fuel.  A forwarding ASSIGN reads every PHI value for the edge,
 * duplicates included, where the input's PHI reads only the first; wf_ssa
 * makes each of them defined at the predecessor's end.
 *)
Theory o1ContractCfgNorm
Ancestors
  o1PassLift cfgNormDefs cfgNormSupplyProofs venomFnScheduleRunner venomWf
  venomInst irSupply

Theorem cfg_norm_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'
Proof
  cheat
QED

(* A split block's ASSIGNs and JMP touch no memory; every other
   instruction keeps its operands up to the renaming of PHI values. *)
Theorem cfg_norm_function_supply_frame_sim:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
Proof
  cheat
QED
