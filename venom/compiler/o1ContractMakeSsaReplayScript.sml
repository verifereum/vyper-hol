(*
 * The O1 dispatcher's MakeSSA step is make_ssa_current_fn run from a
 * supply that covers the function and whose used instruction ids are
 * below its next one (ir_supply_inst_ok), as the per-function MakeSSA
 * lemmas assume.  The dispatcher's supply covers the observed unit but
 * need not have the second property, so the step is replayed from one
 * that has both and gives the same function.
 *)
Theory o1ContractMakeSsaReplay
Ancestors
  o1PassContract makeSsaCurrentDefs venomPassSchedule irSupply

Theorem make_ssa_pass_step_replay:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out ==>
  ?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_current_fn t fn = (out.fpo_function,t')
Proof
  cheat
QED
