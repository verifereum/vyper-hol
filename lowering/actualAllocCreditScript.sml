(* Actual missing allocation sites supply their own weighted credit. *)
Theory actualAllocCredit
Ancestors
  allocaBudgetProps allocaFrontierBound vyperCompiler venomInst venomState
  finite_map list arithmetic words

Theorem remaining_alloca_budget_member:
  !insts inst s.
    MEM inst insts /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id NOTIN FDOM s.vs_allocas ==>
    alloca_size inst <= remaining_alloca_budget insts s
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[remaining_alloca_budget_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[remaining_alloca_budget_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem actual_alloca_frontier_credit:
  !ctx fn site s inst.
    alloca_frontier_inv ctx fn site s /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id NOTIN FDOM s.vs_allocas ==>
    s.vs_alloca_next + alloca_size inst <= unit_alloca_budget ctx
Proof
  rpt strip_tac >> drule_all remaining_alloca_budget_member >>
  gvs[alloca_frontier_inv_def] >> decide_tac
QED

Theorem actual_word_alloca_no_wrap:
  !ctx fn site s inst.
    alloca_frontier_inv ctx fn site s /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ alloca_size inst = 32 /\
    inst.inst_id NOTIN FDOM s.vs_allocas /\
    unit_alloca_budget ctx < dimword (:256) ==>
    s.vs_alloca_next + 32 < dimword (:256)
Proof
  rpt strip_tac >> drule_all actual_alloca_frontier_credit >> simp[]
QED

Theorem actual_word_alloca_fresh_debit:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\ MEM inst insts /\
  inst.inst_opcode = ALLOCA /\ alloca_size inst = 32 /\
  inst.inst_id NOTIN FDOM s.vs_allocas /\
  FDOM t.vs_allocas = inst.inst_id INSERT FDOM s.vs_allocas ==>
  remaining_alloca_budget insts s = 32 + remaining_alloca_budget insts t
Proof
  strip_tac >> drule_all remaining_alloca_budget_fresh_debit >> simp[]
QED

Theorem actual_alloca_reuse_credit:
  inst.inst_opcode = ALLOCA /\ inst.inst_id IN FDOM s.vs_allocas /\
  step_inst_base inst s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next /\
  remaining_alloca_budget insts t = remaining_alloca_budget insts s
Proof
  strip_tac >> drule_all step_inst_base_alloca_effect >> simp[] >>
  strip_tac >> simp[] >> irule remaining_alloca_budget_domain_cong >> simp[]
QED
