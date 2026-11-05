(*
 * MakeSSA's first O1 run keeps the output's taint within the dead
 * bytes D.
 *)
Theory o1ContractMakeSsaTaint
Ancestors
  o1PassContract ptrDiscipline unitMemInv venomPassSchedule list makeSsaCurrentLockstep

Theorem make_ssa_stage_taint:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions ==>
    taint_within D C' vs
Proof
  cheat
QED
