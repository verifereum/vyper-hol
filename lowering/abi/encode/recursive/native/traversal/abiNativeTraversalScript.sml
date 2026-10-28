(* TOP-LEVEL: a native traversal retains its fixed enclosing compiler
   profile, initial state and exact output arena. Remaining compilation is
   supplied by the execution theorem so child endpoints stay inside it. *)
Theory abiNativeTraversal
Ancestors
  abiNativeEncodingDefs abiAllocationWindows abiAllocationTrace abiStateFrame abiMemoryFrame
  abiPathAllocInv allocationPathGrowth allocationGrowth abiWriterFrame abiAllocatedWindows
  compileAllocaProvenance compileIdFlow memoryReadProps
  compileEnv fragExec fragBlockPath venomMemDefs venomState list words arithmetic

Definition abi_native_traversal_def:
  abi_native_traversal ctx func root_cs root_after (root_dst:bytes32) (root_payload:word8 list) initial cs ss <=>
    cs_extends root_cs cs /\ root_cs.cs_next_var <= cs.cs_next_var /\ compiler_id_history cs /\
    fragment_path ctx func initial ss /\
    abi_allocation_trace 32 (compiler_alloca_ids root_cs root_after) initial ss /\
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss) initial ss /\
    (!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==>
      eval_operand arg_op ss = eval_operand arg_op initial) /\
    abi_state_frame initial ss
End

Theorem abi_native_traversal_initial:
  !ctx func cs after dst_addr payload ss.
    compiler_id_history cs ==> abi_native_traversal ctx func cs after dst_addr payload ss cs ss
Proof
  simp[abi_native_traversal_def, abi_allocation_trace_identity, cs_extends_refl]
QED

Theorem abi_native_traversal_allocation:
  !ctx func root_cs root_after root_dst root_payload initial cs ss.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    alloca_inv initial ==> alloca_inv ss /\ allocation_growth initial ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_traversal_def] >> strip_tac >> conj_tac
  >- (drule_all fragment_path_alloca_inv >> simp[]) >>
  drule_all fragment_path_allocation_growth >> simp[]
QED

Theorem abi_native_traversal_source:
  !ctx func root_cs root_after root_dst root_payload initial cs ss
      source_id target_id root_src source_capacity.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    abi_native_memory_ready func root_cs root_after source_id target_id (root_src:bytes32) source_capacity
      root_dst root_payload initial ==>
    mem_bytes_at (w2n root_src) source_capacity ss.vs_memory =
      mem_bytes_at (w2n root_src) source_capacity initial.vs_memory
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_memory_bounds >> strip_tac >>
  `alloca_inv initial /\ ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    abi_allocated_window initial source_id (w2n root_src) source_capacity` by
    fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  `abi_allocated_window ss source_id (w2n root_src) source_capacity` by
    (drule_all allocation_growth_window >> simp[]) >>
  `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  qspecl_then [`compiler_alloca_ids root_cs root_after`, `ss`, `source_id`,
    `w2n root_src`, `source_capacity`] mp_tac abi_allocation_windows_protect_owned >>
  impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qspecl_then [`(w2n root_dst,LENGTH root_payload)::
    abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss`,
    `initial`, `ss`, `w2n root_src`, `source_capacity`] mp_tac abi_memory_frame_read >>
  impl_tac >- simp[] >> simp[read_memory_eq_mem_bytes_at]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native recursive traversal invariant: " ^ name)
  end) (DB.thms "abiNativeTraversal")
