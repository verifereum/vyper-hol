(* TOP-LEVEL: an enclosing traversal preserves any separately owned read
   outside its output arena and computed scratch allocation identities. *)
Theory abiNativeTraversalRead
Ancestors
  abiNativeTraversal abiAllocatedWindows abiAllocationWindows abiWriterFrame abiMemoryFrame
  allocationGrowth compileAllocaProvenance compileEnv venomMemDefs venomState list words

Theorem abi_native_traversal_owned_read:
  !ctx func root_cs root_after root_dst root_payload initial cs ss read_id offset read_len.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\ alloca_inv initial /\
    abi_allocated_window initial read_id offset read_len /\ ~MEM read_id (compiler_alloca_ids root_cs root_after) /\
    abi_window_separated offset read_len (w2n root_dst) (LENGTH root_payload) ==>
    read_memory offset read_len ss = read_memory offset read_len initial
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_allocation >> strip_tac >>
  `abi_allocated_window ss read_id offset read_len` by
    (qspecl_then [`initial`, `ss`, `read_id`, `offset`, `read_len`]
       mp_tac allocation_growth_window >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []) >>
  `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  qspecl_then [`compiler_alloca_ids root_cs root_after`, `ss`, `read_id`, `offset`, `read_len`]
    mp_tac abi_allocation_windows_protect_owned >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qspecl_then [`(w2n root_dst,LENGTH root_payload)::abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss`,
    `initial`, `ss`, `offset`, `read_len`] mp_tac abi_memory_frame_read >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned read through enclosing native traversal: " ^ name)
  end) (DB.thms "abiNativeTraversalRead")
