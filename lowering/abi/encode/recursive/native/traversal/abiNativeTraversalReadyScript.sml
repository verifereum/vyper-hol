(* TOP-LEVEL: enclosing resources prepare any recursive child subwindow,
   independently of aggregate shape. Original-reference source observations
   survive all earlier writes in the actual enclosing traversal. *)
Theory abiNativeTraversalReady
Ancestors
  abiNativeTraversal abiNativeEncodingDefs abiNativeResources abiAllocationBudgetNested
  abiAllocatedWindows abiMemoryEncodingFrame compileAllocaProvenance compileIdFlow
  compileEnv venomState list words arithmetic

Theorem abi_native_traversal_windows:
  !ctx func root_cs root_after source_id target_id root_src source_capacity root_dst root_payload initial cs ss.
    abi_native_memory_ready func root_cs root_after source_id target_id (root_src:bytes32) source_capacity
      root_dst root_payload initial /\
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss ==>
    abi_allocated_window ss source_id (w2n root_src) source_capacity /\
    abi_allocated_window ss target_id (w2n root_dst) (LENGTH root_payload)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  qpat_x_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  conj_tac
  >- (qspecl_then [`32`, `compiler_alloca_ids root_cs root_after`, `initial`, `ss`,
        `source_id`, `w2n root_src`, `source_capacity`] mp_tac abi_allocation_trace_window >> simp[]) >>
  qspecl_then [`32`, `compiler_alloca_ids root_cs root_after`, `initial`, `ss`,
    `target_id`, `w2n root_dst`, `LENGTH root_payload`] mp_tac abi_allocation_trace_window >> simp[]
QED

Theorem abi_native_traversal_call_ready:
  !ctx func root_cs root_after source_id target_id root_src source_capacity root_dst root_payload
      initial reference cs mid ss src_addr mem_sz dst_addr payload source_offset.
    abi_native_memory_ready func root_cs root_after source_id target_id (root_src:bytes32) source_capacity
      root_dst root_payload initial /\
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    cs_extends mid root_after /\
    mem_bytes_at (w2n root_src) source_capacity reference =
      mem_bytes_at (w2n root_src) source_capacity initial.vs_memory /\
    source_offset + mem_sz <= source_capacity /\
    w2n (src_addr:bytes32) = w2n root_src + source_offset /\
    w2n root_dst <= w2n (dst_addr:bytes32) /\
    w2n dst_addr + LENGTH (payload:word8 list) <= w2n root_dst + LENGTH root_payload ==>
    abi_native_memory_ready func cs mid source_id target_id src_addr mem_sz dst_addr payload ss /\
    mem_bytes_at (w2n root_src + source_offset) mem_sz reference =
      mem_bytes_at (w2n root_src + source_offset) mem_sz ss.vs_memory /\
    abi_allocated_window ss source_id (w2n root_src) source_capacity /\
    abi_allocated_window ss target_id (w2n root_dst) (LENGTH root_payload)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_windows >> strip_tac >>
  `mem_bytes_at (w2n root_src) source_capacity ss.vs_memory =
    mem_bytes_at (w2n root_src) source_capacity reference` by
    (qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `root_dst`, `root_payload`, `initial`, `cs`, `ss`,
       `source_id`, `target_id`, `root_src`, `source_capacity`] mp_tac abi_native_traversal_source >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
     DISCH_TAC >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  `w2n root_src <= w2n src_addr /\ w2n src_addr + mem_sz <= w2n root_src + source_capacity` by
    (asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_native_memory_ready func cs mid source_id target_id src_addr mem_sz dst_addr payload ss` by
    (qspecl_then [`func`, `root_cs`, `root_after`, `source_id`, `target_id`, `root_src`, `source_capacity`,
       `root_dst`, `root_payload`, `initial`, `cs`, `mid`, `ss`, `src_addr`, `mem_sz`, `dst_addr`, `payload`]
       mp_tac abi_native_child_ready >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`w2n root_src`, `source_capacity`, `source_offset`, `mem_sz`, `ss.vs_memory`, `reference`]
    mp_tac abi_memory_window_part >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed enclosing native recursive call preparation: " ^ name)
  end) (DB.thms "abiNativeTraversalReady")
