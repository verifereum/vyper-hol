(* TOP-LEVEL: an actual scratch-allocation trace preserves every already
   owned window, including the real output buffer allocated before it. *)
Theory abiAllocationTraceOwned
Ancestors
  abiAllocationTrace abiAllocationSequence abiAllocatedWindows abiAllocatedState abiAllocatorState

Theorem abi_allocation_trace_owned:
  !slot_size ids before after id offset byte_count.
    abi_allocation_trace slot_size ids before after /\ abi_allocated_window before id offset byte_count ==>
    abi_allocated_window after id offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocation_trace _ _ _ _` (mp_tac o REWRITE_RULE [abi_allocation_trace_def]) >>
  disch_then (qx_choose_then `executed` strip_assume_tac) >>
  `abi_allocated_window (abi_allocation_sequence (MAP (\aid. (aid,slot_size)) executed) before) id offset byte_count` by
    (irule abi_allocated_window_sequence >> simp[]) >>
  qspecl_then [`abi_allocation_sequence (MAP (\aid. (aid,slot_size)) executed) before`, `after`, `id`, `offset`, `byte_count`]
    mp_tac abi_allocated_window_state >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation trace ownership preservation: " ^ name)
  end) (DB.thms "abiAllocationTraceOwned")
