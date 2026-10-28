(* TOP-LEVEL: a native child's concrete data and computed scratch windows
   are separated from an owned reader. Distinct allocation identities
   discharge the data separation; same-owner reads use a local interval. *)
Theory abiNativeWriteSeparation
Ancestors
  abiNativeEncodingDefs abiNativeResources abiMemoryFieldsAdvance
  abiAllocationWindows abiAllocatedSeparation abiAllocatedWindows abiWriterFrame abiMemoryFrame
  venomMemDefs venomState compileEnv list words arithmetic

Theorem abi_native_writes_separated:
  !ctx func cs mid ret dst_addr payload ss out read_id read_offset read_len target_id.
    abi_native_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload ss out /\
    alloca_inv ss /\ abi_allocated_window ss read_id read_offset read_len /\
    abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload) /\
    ~MEM read_id (compiler_alloca_ids cs mid) /\
    (target_id = read_id ==> abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload)) ==>
    EVERY (\(write_base,write_count).
      abi_window_separated read_offset read_len write_base write_count)
      (abi_encoding_writes dst_addr payload (abi_allocation_windows (compiler_alloca_ids cs mid) out))
Proof
  rpt gen_tac >> strip_tac >>
  `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload)` by
    (drule_all abi_allocated_window_separated >> simp[]) >>
  drule_all abi_native_result_allocation >> strip_tac >>
  `abi_allocated_window out read_id read_offset read_len` by
    (qspecl_then [`ss`, `out`, `read_id`, `read_offset`, `read_len`]
       mp_tac allocation_growth_window >> simp[]) >>
  `allocas_non_overlapping out` by fs[alloca_inv_def] >>
  qspecl_then [`compiler_alloca_ids cs mid`, `out`, `read_id`, `read_offset`, `read_len`]
    mp_tac abi_allocation_windows_protect_owned >> impl_tac >- simp[] >>
  simp[abi_encoding_writes_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native child write separation: " ^ name)
  end) (DB.thms "abiNativeWriteSeparation")
