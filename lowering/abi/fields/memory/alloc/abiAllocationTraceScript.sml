(* TOP-LEVEL: finite traces of uniform scratch requests compose and may
   replay allocation identities. They preserve the exact pending budget and
   compatible cached requests. Helpers restrict a budget to child profiles.
   Traces describe allocation fields only; memory and SSA frames stay separate. *)
Theory abiAllocationTrace
Ancestors
  abiAllocationBudget abiAllocationFrame abiAllocationSequence abiAllocationSequenceFields
  abiAllocationRequests abiAllocatorState memoryValueSnapshot venomState
  finite_map pred_set list pair arithmetic

Definition abi_allocation_trace_def:
  abi_allocation_trace byte_count ids before after <=>
    ?executed. EVERY (\id. MEM id ids) executed /\
      abi_allocator_state after =
        abi_allocator_state (abi_allocation_sequence (MAP (\id. (id,byte_count)) executed) before)
End

Theorem abi_allocation_trace_identity:
  !byte_count ids before after.
    abi_allocator_state after = abi_allocator_state before ==>
    abi_allocation_trace byte_count ids before after
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_allocation_trace_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem abi_allocation_trace_image:
  !byte_count ids id var_base ss index.
    MEM id ids ==>
    abi_allocation_trace byte_count ids ss
      (memory_snapshot_allocated id var_base byte_count ss with vs_inst_idx := index)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_allocation_trace_def] >>
  qexists_tac `[id]` >>
  simp[abi_allocator_state_def, memory_snapshot_allocated_def, update_var_def]
QED

Theorem abi_allocation_trace_trans:
  !byte_count ids before middle after.
    abi_allocation_trace byte_count ids before middle /\
    abi_allocation_trace byte_count ids middle after ==>
    abi_allocation_trace byte_count ids before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `left` strip_assume_tac)
    (qx_choose_then `right` strip_assume_tac)) >>
  qexists_tac `left ++ right` >> simp[MAP_APPEND, abi_allocation_sequence_append] >>
  qspecl_then [`MAP (\id. (id,byte_count)) right`,
    `abi_allocation_sequence (MAP (\id. (id,byte_count)) left) before`, `middle`]
    mp_tac abi_allocator_state_sequence >> simp[]
QED

Theorem abi_allocation_trace_weaken:
  !byte_count small large before after.
    abi_allocation_trace byte_count small before after /\ set small SUBSET set large ==>
    abi_allocation_trace byte_count large before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >> rpt strip_tac >>
  rename1 `EVERY (\id. MEM id small) executed` >> qexists_tac `executed` >>
  fs[EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_allocation_trace_fields:
  !byte_count ids before after before' after'.
    abi_allocation_trace byte_count ids before after /\
    abi_allocator_state before' = abi_allocator_state before /\
    abi_allocator_state after' = abi_allocator_state after ==>
    abi_allocation_trace byte_count ids before' after'
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >> rpt strip_tac >>
  rename1 `EVERY (\id. MEM id ids) executed` >> qexists_tac `executed` >> simp[] >>
  qspecl_then [`MAP (\id. (id,byte_count)) executed`, `before`, `before'`]
    mp_tac abi_allocator_state_sequence >> simp[]
QED

Theorem abi_allocation_sequence_budget:
  !executed byte_count ids ss.
    EVERY (\id. MEM id ids) executed ==>
    abi_alloca_budget byte_count ids
      (abi_allocation_sequence (MAP (\id. (id,byte_count)) executed) ss) =
      abi_alloca_budget byte_count ids ss
Proof
  Induct_on `executed` >- simp[] >> qx_gen_tac `id` >> rpt gen_tac >>
  simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  simp_tac bool_ss [MAP, abi_allocation_sequence_cons, FST, SND] >>
  `abi_alloca_budget byte_count ids
    (abi_allocation_sequence (MAP (\id. (id,byte_count)) executed)
      (memory_snapshot_alloc_frame id byte_count ss)) =
    abi_alloca_budget byte_count ids (memory_snapshot_alloc_frame id byte_count ss)` by
    (first_x_assum irule >> simp[]) >> simp[abi_alloca_budget_frame]
QED

Theorem abi_alloca_budget_allocator_state:
  !byte_count ids before after.
    abi_allocator_state after = abi_allocator_state before ==>
    abi_alloca_budget byte_count ids after = abi_alloca_budget byte_count ids before
Proof
  simp[abi_allocator_state_def, abi_alloca_budget_def, abi_alloca_pending_def]
QED

Theorem abi_allocation_trace_budget:
  !byte_count ids before after.
    abi_allocation_trace byte_count ids before after ==>
    abi_alloca_budget byte_count ids after = abi_alloca_budget byte_count ids before
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >> strip_tac >>
  rename1 `EVERY (\id. MEM id ids) executed` >>
  irule EQ_TRANS >>
  qexists_tac `abi_alloca_budget byte_count ids
    (abi_allocation_sequence (MAP (\id. (id,byte_count)) executed) before)` >> conj_tac
  >- (irule abi_alloca_budget_allocator_state >> simp[]) >>
  irule abi_allocation_sequence_budget >> simp[]
QED

Theorem abi_allocation_trace_request:
  !byte_count ids before after id.
    abi_allocation_trace byte_count ids before after /\ abi_alloca_request_ok id byte_count before ==>
    abi_alloca_request_ok id byte_count after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >> strip_tac >>
  rename1 `EVERY (\id. MEM id ids) executed` >>
  `abi_alloca_request_ok id byte_count
    (abi_allocation_sequence (MAP (\id. (id,byte_count)) executed) before)` by
    (irule abi_allocation_sequence_request >> simp[EVERY_MAP]) >>
  fs[abi_alloca_request_ok_def, abi_allocator_state_eq]
QED

Theorem abi_alloca_pending_subprofile:
  !small large ss.
    set small SUBSET set large ==>
    abi_alloca_pending small ss SUBSET abi_alloca_pending large ss
Proof
  simp[abi_alloca_pending_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_alloca_budget_subprofile:
  !byte_count small large ss.
    set small SUBSET set large ==>
    abi_alloca_budget byte_count small ss <= abi_alloca_budget byte_count large ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `CARD (abi_alloca_pending small ss) <= CARD (abi_alloca_pending large ss)` by
    (irule CARD_SUBSET >> simp[] >> irule abi_alloca_pending_subprofile >> simp[]) >>
  qspecl_then [`CARD (abi_alloca_pending small ss)`, `CARD (abi_alloca_pending large ss)`, `byte_count`]
    mp_tac LESS_MONO_MULT >> simp[abi_alloca_budget_def, MULT_COMM]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed reusable ABI allocation trace budget: " ^ name)
  end) (DB.thms "abiAllocationTrace")
