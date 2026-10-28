(* TOP-LEVEL: caller-local requests retain their reservation, while
   unrecorded frontier growth consumes explicit credit. Internal calls
   restore the caller's allocation map and use this charged transition. *)
Theory abiRequestCredit
Ancestors
  abiRequestProfile abiRequestTrace abiAllocationBudgetBounds abiAllocationBudget
  abiAllocationSequence abiAllocatorState abiAllocationFrame abiStepAllocRecords
  allocationPathGrowth allocationGrowth memoryValueSnapshot
  compileEnv venomMemDefs venomExecSemantics venomState venomInst list pair words arithmetic

Definition abi_request_credit_def:
  abi_request_credit reserved requests credit ss <=>
    abi_requests_consistent requests /\ EVERY (\request. SND request <= reserved) requests /\
    abi_requests_compatible requests ss /\
    abi_alloca_budget reserved (MAP FST requests) ss + reserved + credit < dimword(:256)
End

Theorem abi_request_credit_zero:
  !reserved requests ss.
    abi_request_credit reserved requests 0 ss <=> abi_request_reservation reserved requests ss
Proof
  simp[abi_request_credit_def, abi_request_reservation_def]
QED

Theorem abi_request_credit_reservation:
  !reserved requests credit ss.
    abi_request_credit reserved requests credit ss ==> abi_request_reservation reserved requests ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_request_credit_def, abi_request_reservation_def] >>
  strip_tac >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_request_credit_allocator_state:
  !reserved requests credit before after.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_request_credit reserved requests credit after <=> abi_request_credit reserved requests credit before)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  simp[abi_request_credit_def, abi_requests_compatible_def, abi_alloca_request_ok_def,
    abi_alloca_budget_def, abi_alloca_pending_def]
QED

Theorem abi_request_credit_frame:
  !reserved requests credit id byte_count ss.
    abi_request_credit reserved requests credit ss /\ MEM (id,byte_count) requests ==>
    abi_request_credit reserved requests credit (memory_snapshot_alloc_frame id byte_count ss)
Proof
  rpt gen_tac >> strip_tac >> fs[abi_request_credit_def] >>
  `byte_count <= reserved` by
    (qpat_x_assum `EVERY (\request. SND request <= reserved) requests`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then (qspec_then `(id,byte_count)` mp_tac) >> simp[]) >>
  `MEM id (MAP FST requests)` by (simp[MEM_MAP] >> qexists_tac `(id,byte_count)` >> simp[]) >>
  qspecl_then [`reserved`, `MAP FST requests`, `id`, `byte_count`, `ss`]
    mp_tac abi_alloca_budget_frame_bound >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `abi_requests_compatible requests (memory_snapshot_alloc_frame id byte_count ss)` by
    (drule_all abi_requests_compatible_frame >> simp[]) >>
  simp_tac bool_ss [abi_request_credit_def] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_request_credit_charge:
  !reserved requests credit before after spent.
    abi_request_credit reserved requests credit before /\ after.vs_allocas = before.vs_allocas /\
    before.vs_alloca_next + spent = after.vs_alloca_next /\ spent <= credit ==>
    abi_request_credit reserved requests (credit - spent) after
Proof
  rpt gen_tac >> strip_tac >> fs[abi_request_credit_def] >>
  `abi_requests_compatible requests after` by
    (qpat_x_assum `abi_requests_compatible _ _` mp_tac >>
     asm_simp_tac bool_ss [abi_requests_compatible_def, abi_alloca_request_ok_def]) >>
  `abi_alloca_budget reserved (MAP FST requests) after =
    abi_alloca_budget reserved (MAP FST requests) before + spent` by
    (asm_simp_tac bool_ss [abi_alloca_budget_def, abi_alloca_pending_def] >> decide_tac) >>
  simp_tac bool_ss [abi_request_credit_def] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_request_credit_sequence:
  !executed reserved requests credit ss.
    EVERY (\request. MEM request requests) executed /\ abi_request_credit reserved requests credit ss ==>
    abi_request_credit reserved requests credit (abi_allocation_sequence executed ss)
Proof
  Induct_on `executed` >- simp[] >> rpt gen_tac >>
  rename1 `EVERY _ (request::rest)` >> Cases_on `request` >>
  simp_tac (srw_ss()) [abi_allocation_sequence_cons] >> strip_tac >>
  first_x_assum irule >> simp[abi_request_credit_frame]
QED

Theorem abi_request_trace_credit:
  !requests before after reserved credit.
    abi_request_trace requests before after /\ abi_request_credit reserved requests credit before ==>
    abi_request_credit reserved requests credit after
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_request_trace _ _ _` (mp_tac o REWRITE_RULE [abi_request_trace_def]) >>
  disch_then (qx_choose_then `executed` strip_assume_tac) >>
  `abi_request_credit reserved requests credit (abi_allocation_sequence executed before)` by
    (irule abi_request_credit_sequence >> simp[]) >>
  qspecl_then [`reserved`, `requests`, `credit`, `abi_allocation_sequence executed before`, `after`]
    mp_tac abi_request_credit_allocator_state >> simp[]
QED

Theorem invoke_request_credit:
  !fuel ctx inst before after reserved requests credit.
    inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst before = OK after /\ alloca_inv before /\
    abi_request_credit reserved requests credit before /\ after.vs_alloca_next - before.vs_alloca_next <= credit ==>
    abi_request_credit reserved requests (credit - (after.vs_alloca_next - before.vs_alloca_next)) after
Proof
  rpt gen_tac >> strip_tac >> drule_all step_inst_invoke_allocas >> DISCH_TAC >>
  drule_all step_inst_allocation_growth >> DISCH_TAC >>
  `before.vs_alloca_next <= after.vs_alloca_next` by (drule_all allocation_growth_next >> simp[]) >>
  qspecl_then [`reserved`, `requests`, `credit`, `before`, `after`, `after.vs_alloca_next - before.vs_alloca_next`]
    mp_tac abi_request_credit_charge >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation credit for caller and callee frames: " ^ name)
  end) (DB.thms "abiRequestCredit")
