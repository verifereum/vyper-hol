(* TOP-LEVEL: a uniform reservation bounds a heterogeneous sequence of
   actual requests. Smaller requests consume at most their reserved share;
   cached requests do not increase the budget. *)
Theory abiAllocationBudgetBounds
Ancestors
  abiAllocationBudget abiAllocationSequence abiAllocationFrame memoryValueSnapshot
  venomState finite_map list pair arithmetic

Theorem abi_alloca_budget_frame_bound:
  !reserved ids id byte_count ss.
    MEM id ids /\ byte_count <= reserved ==>
    abi_alloca_budget reserved ids (memory_snapshot_alloc_frame id byte_count ss) <=
    abi_alloca_budget reserved ids ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP ss.vs_allocas id = NONE`
  >- (drule_all abi_alloca_pending_delete_card >> DISCH_TAC >>
      simp_tac bool_ss [abi_alloca_budget_def, abi_alloca_pending_frame] >>
      asm_simp_tac bool_ss [memory_snapshot_alloc_frame_def, venom_state_accfupds,
        combinTheory.K_THM, MULT_CLAUSES, ADD_ASSOC] >> decide_tac) >>
  simp[memory_snapshot_alloc_frame_def]
QED

Theorem abi_allocation_sequence_budget_bound:
  !executed reserved ids ss.
    EVERY (\request. MEM (FST request) ids /\ SND request <= reserved) executed ==>
    abi_alloca_budget reserved ids (abi_allocation_sequence executed ss) <=
    abi_alloca_budget reserved ids ss
Proof
  Induct_on `executed` >- simp[] >> rpt gen_tac >>
  rename1 `EVERY _ (request::rest)` >>
  simp_tac bool_ss [EVERY_DEF, abi_allocation_sequence_cons] >> strip_tac >>
  `abi_alloca_budget reserved ids
    (abi_allocation_sequence rest (memory_snapshot_alloc_frame (FST request) (SND request) ss)) <=
    abi_alloca_budget reserved ids (memory_snapshot_alloc_frame (FST request) (SND request) ss)` by
    (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`reserved`, `ids`, `FST request`, `SND request`, `ss`] mp_tac abi_alloca_budget_frame_bound >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> decide_tac
QED

Theorem abi_alloca_budget_request_room:
  !reserved ids ss byte_count.
    abi_alloca_budget reserved ids ss + reserved < dimword(:256) /\ byte_count <= reserved ==>
    ss.vs_alloca_next + byte_count < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`reserved`, `ids`, `ss`] mp_tac abi_alloca_budget_frontier >> decide_tac
QED
