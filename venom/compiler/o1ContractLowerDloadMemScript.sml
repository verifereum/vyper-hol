(*
 * LowerDload against the O1 pass contract: the output keeps raw memory
 * safety on its reachable states.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_mem
 *)
Theory o1ContractLowerDloadMem
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list

(* The output's reachable states keep raw memory safety. *)
Theorem lower_dload_stage_mem:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    mem_inv raw_mem_ok C' vs
Proof
  cheat
QED
