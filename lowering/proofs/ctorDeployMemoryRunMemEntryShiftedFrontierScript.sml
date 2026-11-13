Theory ctorDeployMemoryRunMemEntryShiftedFrontier
Ancestors
  ctorDeployMemoryFrontier actualAllocCredit allocaFrontierBound
  allocaBudgetProps venomInst venomState finite_map pred_set list arithmetic words

(* The deployment's immutables region is reserved before the first ALLOCA;
   credit is measured against the shifted total, without moving any address. *)
Theorem actual_alloca_frontier_credit_from:
  !k ctx fn site s inst.
    alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id NOTIN FDOM s.vs_allocas ==>
    s.vs_alloca_next + alloca_size inst <= k + unit_alloca_budget ctx
Proof
  rpt strip_tac >> drule_all remaining_alloca_budget_member >>
  gvs[alloca_frontier_inv_from_def] >> decide_tac
QED

Theorem actual_alloca_no_wrap_from:
  !k ctx fn site s inst.
    alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id NOTIN FDOM s.vs_allocas /\
    k + unit_alloca_budget ctx < dimword (:256) ==>
    s.vs_alloca_next + alloca_size inst < dimword (:256)
Proof
  rpt strip_tac >> drule_all actual_alloca_frontier_credit_from >> simp[]
QED

Theorem actual_word_alloca_no_wrap_from:
  !k ctx fn site s inst.
    alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ alloca_size inst = 32 /\
    inst.inst_id NOTIN FDOM s.vs_allocas /\
    k + unit_alloca_budget ctx < dimword (:256) ==>
    s.vs_alloca_next + 32 < dimword (:256)
Proof
  rpt strip_tac >> drule_all actual_alloca_no_wrap_from >> simp[]
QED
