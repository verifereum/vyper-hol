(* TOP-LEVEL: mixed-field traversal invariants use existing source/output
   allocation ownership, a compiler scratch-request profile, and the remaining
   native scratch budget. They contain no future execution assumptions. *)
Theory abiFieldStateDefs
Ancestors
  abiFieldRequests abiFieldDefs abiFieldLayoutDefs abiFieldMemory abiAllocatedWindows abiAllocationFrame
  compileEnv venomMemDefs venomState list words arithmetic

Definition abi_field_budget_def:
  abi_field_budget (AbiFieldFlat row) = 0 /\
  abi_field_budget (AbiFieldDynBytes ty tv capacity vs bss) = 96
End

Definition abi_field_geometry_def:
  abi_field_geometry fields rows tail_start capacity <=>
    abi_field_head_size fields + abi_field_head_size (MAP abi_field_output rows) <= tail_start /\
    tail_start + abi_field_tail_size fields + abi_field_tail_size (MAP abi_field_output rows) <= capacity
End

Definition abi_field_state_def:
  abi_field_state tenv fields rows tail_start dst_addr (dyn_addr:bytes32) root_addr source_offset capacity
      source_id target_id dyn_id next_id ss <=>
    EVERY (abi_field_valid tenv) rows /\ alloca_inv ss /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) ss) (abi_field_requests next_id rows) /\
    EVERY (\id. id < next_id) [source_id;target_id;dyn_id] /\
    ss.vs_alloca_next + SUM (MAP abi_field_budget rows) < dimword(:256) /\
    ALL_DISTINCT [source_id;target_id;dyn_id] /\
    abi_allocated_window ss target_id (w2n dst_addr) capacity /\ abi_allocated_window ss dyn_id (w2n dyn_addr) 32 /\
    abi_field_geometry fields rows tail_start capacity /\ abi_fields_layout fields (w2n dst_addr) 0 tail_start ss /\
    mload (w2n dyn_addr) ss = n2w (tail_start + abi_field_tail_size fields) /\
    abi_field_sources rows source_id root_addr source_offset dst_addr (tail_start + abi_field_tail_size fields) ss
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-owned mixed traversal invariant: " ^ name)
  end) (DB.thms "abiFieldStateDefs")
