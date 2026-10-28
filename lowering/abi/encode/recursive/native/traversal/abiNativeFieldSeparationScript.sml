(* TOP-LEVEL: concrete field writes, including parent stores, are
   separated from any owned read after their actual allocation growth. *)
Theory abiNativeFieldSeparation
Ancestors
  abiMemoryLeafRun abiMemoryFieldsAdvance abiAllocatedSeparation abiAllocatedWindows
  abiAllocationWindows abiWriterFrame abiMemoryFrame abiPathAllocInv allocationPathGrowth
  compileAllocaProvenance compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_field_separated:
  !ctx func cs mid ret dst_addr payload extra ss out read_id read_offset read_len target_id.
    abi_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload
      (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra) ss out /\
    alloca_inv ss /\ abi_allocated_window ss read_id read_offset read_len /\
    abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload) /\
    ~MEM read_id (compiler_alloca_ids cs mid) /\
    (target_id = read_id ==> abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload)) /\
    EVERY (\(write_base,write_count). abi_window_separated read_offset read_len write_base write_count) extra ==>
    EVERY (\(write_base,write_count). abi_window_separated read_offset read_len write_base write_count)
      (abi_encoding_writes dst_addr payload (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra))
Proof
  rpt gen_tac >> strip_tac >>
  `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `abi_window_separated read_offset read_len (w2n dst_addr) (LENGTH payload)` by
    (drule_all abi_allocated_window_separated >> simp[]) >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `alloca_inv out` by
    (qspecl_then [`ctx`, `func`, `ss`, `out`] mp_tac fragment_path_alloca_inv >> simp[]) >>
  `allocation_growth ss out` by
    (qspecl_then [`ctx`, `func`, `ss`, `out`] mp_tac fragment_path_allocation_growth >> simp[]) >>
  `abi_allocated_window out read_id read_offset read_len` by
    (qspecl_then [`ss`, `out`, `read_id`, `read_offset`, `read_len`]
       mp_tac allocation_growth_window >> simp[]) >>
  `allocas_non_overlapping out` by fs[alloca_inv_def] >>
  qspecl_then [`compiler_alloca_ids cs mid`, `out`, `read_id`, `read_offset`, `read_len`]
    mp_tac abi_allocation_windows_protect_owned >> impl_tac >- simp[] >>
  simp[abi_encoding_writes_def, EVERY_APPEND]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned complete field write separation: " ^ name)
  end) (DB.thms "abiNativeFieldSeparation")
