(* TOP-LEVEL: allocation sequences depend on allocation records and frontier,
   so register-only navigation leaves every future scratch address unchanged. *)
Theory abiAllocationSequenceFields
Ancestors
  abiAllocationSequence abiAllocationFrame memoryValueSnapshot venomState list pair

Theorem abi_allocation_sequence_fields:
  !allocations before after.
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next ==>
    (abi_allocation_sequence allocations after).vs_allocas = (abi_allocation_sequence allocations before).vs_allocas /\
    (abi_allocation_sequence allocations after).vs_alloca_next = (abi_allocation_sequence allocations before).vs_alloca_next
Proof
  Induct_on `allocations` >- simp[] >> qx_gen_tac `allocation` >> rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [abi_allocation_sequence_cons] >> first_x_assum irule >>
  mp_tac (Q.SPECL [`before`, `after`, `FST (allocation:num # num)`, `SND (allocation:num # num)`]
    abi_allocation_frame_fields) >> simp[]
QED

Theorem abi_allocation_sequence_address:
  !allocations before after id.
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next ==>
    memory_snapshot_addr id (abi_allocation_sequence allocations after) =
      memory_snapshot_addr id (abi_allocation_sequence allocations before)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_allocation_sequence_fields >>
  simp[memory_snapshot_addr_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-sequence field dependence: " ^ name)
  end) (DB.thms "abiAllocationSequenceFields")
