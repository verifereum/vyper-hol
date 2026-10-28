(* TOP-LEVEL: a pending-identity budget supplies all bounds needed by an
   actual allocation, even when a cached slot is near the word frontier.
   Helper: cached records need only the existing frontier to be in range. *)
Theory abiAllocationBudgetReady
Ancestors
  abiAllocationBudget abiAllocationFrame memoryValueSnapshot
  venomMemDefs venomState finite_map words arithmetic

Theorem abi_allocation_record:
  !id byte_count ss.
    abi_alloca_request_ok id byte_count ss /\ alloca_inv ss /\
    ss.vs_alloca_next < dimword (:256) /\
    (FLOOKUP ss.vs_allocas id = NONE ==> ss.vs_alloca_next + byte_count < dimword (:256)) ==>
    ?offset recorded_size.
      FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas id = SOME (offset,recorded_size) /\
      byte_count <= recorded_size /\ w2n (memory_snapshot_addr id ss) = offset /\
      offset + recorded_size <= (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP ss.vs_allocas id`
  >- (fs[] >> qspecl_then [`id`, `byte_count`, `ss`] mp_tac abi_allocation_frame_record >>
      impl_tac >- simp[] >> simp[]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME region` >> PairCases_on `region` >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size)` >>
  `byte_count <= recorded_size` by fs[abi_alloca_request_ok_def] >>
  `offset + recorded_size <= ss.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `offset < dimword (:256)` by decide_tac >> qexistsl_tac [`offset`, `recorded_size`] >>
  fs[memory_snapshot_alloc_frame_def, memory_snapshot_addr_def]
QED

Theorem abi_alloca_budget_ready:
  !byte_count ids id ss.
    MEM id ids /\ abi_alloca_budget byte_count ids ss < dimword (:256) /\
    abi_alloca_request_ok id byte_count ss /\ alloca_inv ss ==>
    byte_count < dimword (:256) /\
    alloca_inv (memory_snapshot_alloc_frame id byte_count ss) /\
    abi_alloca_budget byte_count ids (memory_snapshot_alloc_frame id byte_count ss) =
      abi_alloca_budget byte_count ids ss /\
    (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next < dimword (:256) /\
    ?offset recorded_size.
      FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas id = SOME (offset,recorded_size) /\
      byte_count <= recorded_size /\ w2n (memory_snapshot_addr id ss) = offset /\
      offset + recorded_size <= (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `abi_alloca_budget byte_count ids (memory_snapshot_alloc_frame id byte_count ss) =
    abi_alloca_budget byte_count ids ss` by (irule abi_alloca_budget_frame >> simp[]) >>
  `ss.vs_alloca_next < dimword (:256)` by
    (qspecl_then [`byte_count`, `ids`, `ss`] mp_tac abi_alloca_budget_frontier >> decide_tac) >>
  `(memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next < dimword (:256)` by
    (qspecl_then [`byte_count`, `ids`, `memory_snapshot_alloc_frame id byte_count ss`]
       mp_tac abi_alloca_budget_frontier >> simp[] >> decide_tac) >>
  `FLOOKUP ss.vs_allocas id = NONE ==> ss.vs_alloca_next + byte_count < dimword (:256)` by
    (DISCH_TAC >> qspecl_then [`byte_count`, `ids`, `id`, `ss`] mp_tac abi_alloca_budget_fresh >>
     impl_tac >- simp[] >> decide_tac) >>
  drule_all abi_allocation_record >>
  disch_then (qx_choose_then `offset` (qx_choose_then `recorded_size` strip_assume_tac)) >>
  `byte_count < dimword (:256)` by decide_tac >>
  `alloca_inv (memory_snapshot_alloc_frame id byte_count ss)` by
    (irule abi_allocation_frame_inv >> simp[]) >>
  simp[] >> qexistsl_tac [`offset`, `recorded_size`] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed cached ABI allocation readiness: " ^ name)
  end) (DB.thms "abiAllocationBudgetReady")
