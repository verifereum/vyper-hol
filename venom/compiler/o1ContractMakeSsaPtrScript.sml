(*
 * MakeSSA's first O1 run keeps the pointer discipline above the same
 * fixed region.  It renames variables and adds PHIs and ASSIGNs between
 * them, and touches no memory operation.
 *)
Theory o1ContractMakeSsaPtr
Ancestors
  o1PassContract ptrDiscipline unitMemInv venomPassSchedule list makeSsaCurrentOrigin

Theorem make_ssa_stage_ptr:
  !rpolicy D view C C' vs names lo.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs ==>
    ptr_discipline lo C' vs
Proof
  cheat
QED
