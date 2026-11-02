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
  venomFnScheduleRunner venomWf venomInst irSupply

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
  frame_sim L C C' fn fn'
Proof
  cheat
QED
