(* TOP-LEVEL: an enclosing encoder's fixed allocation budget supplies every
   recursive child's current budget and request compatibility, after any
   finite replay of its scratch identities. Helpers transport allocator
   invariants and old owned windows through the same allocation trace. *)
Theory abiAllocationBudgetNested
Ancestors
  abiAllocationTrace abiAllocationBudget abiAllocationFrame abiAllocationSequence
  abiAllocatorState abiAllocatedWindows compileAllocaProfiles compileAllocaProvenance
  compileEnv venomMemDefs venomState list pred_set words arithmetic
Libs wordsLib

Theorem abi_allocation_trace_inv:
  !byte_count ids before after.
    byte_count < dimword (:256) /\ alloca_inv before /\
    abi_allocation_trace byte_count ids before after ==> alloca_inv after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >> strip_tac >>
  rename1 `EVERY (\id. MEM id ids) executed` >>
  fs[abi_allocator_state_eq] >> irule abi_allocation_fields_inv >>
  qexists_tac `abi_allocation_sequence (MAP (\id. (id,byte_count)) executed) before` >>
  simp[] >> irule abi_allocation_sequence_inv >> simp[EVERY_MAP]
QED

Theorem abi_allocation_trace_window:
  !byte_count ids before after id offset byte_count'.
    abi_allocation_trace byte_count ids before after /\
    abi_allocated_window before id offset byte_count' ==>
    abi_allocated_window after id offset byte_count'
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def] >> strip_tac >>
  rename1 `EVERY (\id. MEM id ids) executed` >>
  `abi_allocated_window (abi_allocation_sequence (MAP (\id. (id,byte_count)) executed) before)
    id offset byte_count'` by (irule abi_allocated_window_sequence >> simp[]) >>
  fs[abi_allocator_state_eq, abi_allocated_window_def]
QED

Theorem abi_compiled_child_allocation_ready:
  !before child_before child_after after initial current.
    cs_extends before child_before /\ cs_extends child_after after /\
    abi_allocation_trace 32 (compiler_alloca_ids before after) initial current /\
    abi_alloca_budget 32 (compiler_alloca_ids before after) initial < dimword (:256) /\
    alloca_inv initial /\
    (!id. MEM id (compiler_alloca_ids before after) ==> abi_alloca_request_ok id 32 initial) ==>
    alloca_inv current /\
    abi_alloca_budget 32 (compiler_alloca_ids child_before child_after) current < dimword (:256) /\
    !id. MEM id (compiler_alloca_ids child_before child_after) ==> abi_alloca_request_ok id 32 current
Proof
  rpt gen_tac >> strip_tac >>
  `set (compiler_alloca_ids child_before child_after) SUBSET set (compiler_alloca_ids before after)` by
    (irule compiler_alloca_profile_subprofile >> simp[]) >>
  `abi_alloca_budget 32 (compiler_alloca_ids before after) current =
    abi_alloca_budget 32 (compiler_alloca_ids before after) initial` by
    (irule abi_allocation_trace_budget >> simp[]) >>
  `abi_alloca_budget 32 (compiler_alloca_ids child_before child_after) current <=
    abi_alloca_budget 32 (compiler_alloca_ids before after) current` by
    (irule abi_alloca_budget_subprofile >> simp[]) >>
  `abi_alloca_budget 32 (compiler_alloca_ids child_before child_after) current < dimword (:256)` by
    decide_tac >>
  `32 < dimword (:256)` by simp_tac (srw_ss() ++ SIZES_ss) [] >>
  `alloca_inv current` by
    (qspecl_then [`32`, `compiler_alloca_ids before after`, `initial`, `current`]
       mp_tac abi_allocation_trace_inv >> simp[]) >>
  simp[] >> qx_gen_tac `id` >> DISCH_TAC >>
  `MEM id (compiler_alloca_ids before after)` by fs[SUBSET_DEF] >>
  `abi_alloca_request_ok id 32 initial` by
    (qpat_x_assum `!id. _` (qspec_then `id` mp_tac) >> simp[]) >>
  qspecl_then [`32`, `compiler_alloca_ids before after`, `initial`, `current`, `id`]
    mp_tac abi_allocation_trace_request >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed nested recursive ABI allocation readiness: " ^ name)
  end) (DB.thms "abiAllocationBudgetNested")
