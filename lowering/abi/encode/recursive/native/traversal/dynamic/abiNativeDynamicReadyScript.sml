(* TOP-LEVEL: computed mixed-field offsets and enclosing resources prepare
   the actual static-head or dynamic-tail recursive call from its original
   reference memory. Both choices retain complete source/output ownership. *)
Theory abiNativeDynamicReady
Ancestors
  abiNativeDynamicBounds abiNativeTraversalReady abiNativeTraversal abiNativeEncodingDefs
  abiMemoryFieldsState abiFieldLayoutDefs abiAllocatedWindows compileEnv venomState list words arithmetic

Theorem abi_native_dynamic_call_ready:
  !ctx func root_cs root_after source_id target_id initial reference full done payload fields
      dst_addr dyn_addr root_addr source_capacity source_offset info abi_sz mem_sz is_dyn rest cs mid ss.
    full = done ++ ((is_dyn,payload)::fields) /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    cs_extends mid root_after /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss ==>
    abi_native_memory_ready func cs mid source_id target_id (root_addr + n2w source_offset) mem_sz
      (if is_dyn then dst_addr + mload (w2n dyn_addr) ss else dst_addr + n2w (abi_field_head_size done))
      payload ss /\
    mem_bytes_at (w2n root_addr + source_offset) mem_sz reference =
      mem_bytes_at (w2n root_addr + source_offset) mem_sz ss.vs_memory /\
    abi_allocated_window ss source_id (w2n root_addr) source_capacity /\
    abi_allocated_window ss target_id (w2n dst_addr)
      (LENGTH (abi_field_bytes (abi_field_head_size full) full))
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_field_bounds >> strip_tac >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`,
    `dst_addr`, `abi_field_bytes (abi_field_head_size full) full`, `initial`, `reference`, `cs`, `mid`, `ss`,
    `root_addr + n2w source_offset`, `mem_sz`,
    `if is_dyn then dst_addr + mload (w2n dyn_addr) ss else dst_addr + n2w (abi_field_head_size done)`,
    `payload`, `source_offset`] mp_tac abi_native_traversal_call_ready >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed mixed native traversal call preparation: " ^ name)
  end) (DB.thms "abiNativeDynamicReady")
