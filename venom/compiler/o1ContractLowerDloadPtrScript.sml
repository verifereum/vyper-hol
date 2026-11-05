(*
 * LowerDload against the O1 pass contract: the output keeps the pointer
 * discipline above the same fixed region.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_ptr
 *)
Theory o1ContractLowerDloadPtr
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list

(* The output keeps the pointer discipline above the same fixed region. *)
Theorem lower_dload_stage_ptr:
  !rpolicy D view C C' vs names lo.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs ==>
    ptr_discipline lo C' vs
Proof
  cheat
QED
