(* TOP-LEVEL: actual field execution with a parent head/cursor store
   advances enclosing execution and cursor ownership. All field writes
   fit the enclosing data window and computed allocation profile. *)
Theory abiNativeCursorStep
Ancestors
  abiNativeCursor abiNativeCursorFrame abiNativeFieldFrame abiNativeTraversal abiNativeTraversalStep
  abiMemoryLeafRun abiAllocationWindows abiMemoryFrame abiPathAllocInv allocationPathGrowth
  compileAllocaProvenance compileIdFlow compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_cursor_traversal_step:
  !ctx func root_cs root_after root_dst root_payload initial counter_inst dyn_addr cs mid ret
      dst_addr payload head_base ss out.
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial cs ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\ alloca_inv initial /\
    abi_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload
      (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ [(head_base,32);(w2n dyn_addr,32)]) ss out /\
    abi_allocation_trace 32 (compiler_alloca_ids cs mid) ss out /\
    cs_extends cs mid /\ cs_extends mid root_after /\ cs.cs_next_var <= mid.cs_next_var /\ compiler_id_history mid /\
    w2n root_dst <= w2n dst_addr /\ w2n dst_addr + LENGTH payload <= w2n root_dst + LENGTH root_payload /\
    w2n root_dst <= head_base /\ head_base + 32 <= w2n root_dst + LENGTH root_payload ==>
    abi_native_traversal ctx func root_cs root_after root_dst root_payload initial mid out /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr mid out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  `cs_extends root_cs cs` by
    (qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `allocation_growth ss out` by
    (qspecl_then [`ctx`, `func`, `ss`, `out`] mp_tac fragment_path_allocation_growth >> simp[]) >>
  drule_all abi_native_cursor_step >> DISCH_TAC >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `dyn_addr`, `mid`, `out`,
    `root_dst`, `root_payload`, `head_base`] mp_tac abi_native_cursor_stores_cover >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `root_dst`, `root_payload`, `cs`, `mid`, `ret`,
    `dst_addr`, `payload`, `[(head_base,32);(w2n dyn_addr,32)]`, `ss`, `out`]
    mp_tac abi_native_field_frame >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `root_dst`, `root_payload`, `initial`, `cs`, `mid`, `ret`,
    `dst_addr`, `payload`, `abi_allocation_windows (compiler_alloca_ids cs mid) out ++
      [(head_base,32);(w2n dyn_addr,32)]`, `ss`, `out`] mp_tac abi_native_traversal_step >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual parent cursor traversal advancement: " ^ name)
  end) (DB.thms "abiNativeCursorStep")
