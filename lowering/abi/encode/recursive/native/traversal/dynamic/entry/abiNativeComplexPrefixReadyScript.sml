(* TOP-LEVEL: the actual prefix establishes cursor ownership and the
   enclosing traversal invariant from the native encoder's resources.
   Helper: an owned cursor store fits its enclosing computed profile. *)
Theory abiNativeComplexPrefixReady
Ancestors
  abiNativeComplexPrefixState abiNativeComplexPrefixCode abiNativeEncodingDefs abiNativeCursor abiNativeTraversal
  abiComplexCode abiComplexStructure abiStaticLoopCode abiAllocatedWindows abiAllocationWindows abiMemoryFrameCover
  abiMemoryFrame abiAllocationBudget abiAllocationFrame compileAllocaProvenance compileIdFlow compileEnv
  venomMemDefs venomState venomInst finite_map list words arithmetic

Theorem abi_native_complex_entry_cursor:
  !func cs after head_size ss.
    compiler_id_history cs /\ fn_has_code cs (abi_complex_prefix_cut head_size cs) func /\
    cs_extends (abi_complex_prefix_cut head_size cs) after /\
    abi_allocated_window (abi_native_complex_entry head_size cs ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 ==>
    abi_native_cursor func cs after (abi_native_complex_counter_inst cs)
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_complex_prefix_cut head_size cs)
      (abi_native_complex_entry head_size cs ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_complex_prefix_provenance >> strip_tac >>
  simp_tac bool_ss [abi_native_cursor_def] >> asm_simp_tac (srw_ss()) [abi_native_complex_counter_inst_def, mk_inst_def]
QED

Theorem abi_native_cursor_store_frame:
  !func root_cs root_after counter_inst dyn_addr cs before current root_dst root_payload.
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs current /\
    abi_memory_frame [(w2n dyn_addr,32)] before current ==>
    abi_memory_frame ((w2n (root_dst:bytes32),LENGTH (root_payload:word8 list))::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) current) before current
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qpat_x_assum `abi_allocated_window _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP current.vs_allocas counter_inst.inst_id = SOME (cursor_base,cursor_capacity)` >>
  irule abi_memory_frame_cover >> qexists_tac `[(w2n dyn_addr,32)]` >> conj_tac
  >- (simp_tac bool_ss [abi_writes_cover_def, MEM] >>
      MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> strip_tac >> gvs[] >>
      qexistsl_tac [`cursor_base`, `cursor_capacity`] >> conj_tac
      >- (simp_tac bool_ss [MEM] >> disj2_tac >>
          simp_tac bool_ss [abi_allocation_windows_member] >> qexists_tac `counter_inst.inst_id` >> simp[]) >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_complex_entry_traversal:
  !ctx func cs after source_id target_id src_addr source_capacity dst_addr payload head_size ss.
    abi_native_memory_ready func cs after source_id target_id src_addr source_capacity dst_addr payload ss /\
    fn_has_code cs (abi_complex_prefix_cut head_size cs) func /\
    cs_extends (abi_complex_prefix_cut head_size cs) after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    abi_native_traversal ctx func cs after dst_addr payload ss (abi_complex_prefix_cut head_size cs)
      (abi_native_complex_entry head_size cs ss) /\
    abi_native_cursor func cs after (abi_native_complex_counter_inst cs)
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_complex_prefix_cut head_size cs)
      (abi_native_complex_entry head_size cs ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  drule_all abi_native_complex_prefix_provenance >> strip_tac >>
  `MEM cs.cs_next_id (compiler_alloca_ids cs after)` by
    fs[abi_native_complex_counter_inst_def, mk_inst_def] >>
  `abi_alloca_request_ok cs.cs_next_id 32 ss` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`head_size`, `cs`, `compiler_alloca_ids cs after`, `ss`]
    mp_tac abi_native_complex_entry_allocation >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_complex_entry_cursor >> DISCH_TAC >>
  qspecl_then [`head_size`, `cs`, `ss`] strip_assume_tac abi_native_complex_entry_context >>
  qspecl_then [`func`, `cs`, `after`, `abi_native_complex_counter_inst cs`,
    `abi_static_loop_counter_addr cs.cs_next_id ss`, `abi_complex_prefix_cut head_size cs`, `ss`,
    `abi_native_complex_entry head_size cs ss`, `dst_addr`, `payload`] mp_tac abi_native_cursor_store_frame >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  drule_all abi_native_complex_entry_path >> DISCH_TAC >>
  `compiler_id_history (abi_complex_prefix_cut head_size cs)` by
    (drule_all abi_native_complex_prefix_history >> simp[]) >>
  `cs_extends cs (abi_complex_prefix_cut head_size cs) /\
    cs.cs_next_var <= (abi_complex_prefix_cut head_size cs).cs_next_var` by
    simp[abi_complex_prefix_extends, abi_complex_prefix_cut_def] >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_complex_entry head_size cs ss) = eval_operand arg_op ss` by
    (rpt strip_tac >> drule_all abi_native_complex_entry_old_operand >> simp[]) >>
  conj_tac >- (simp_tac bool_ss [abi_native_traversal_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual complex prefix native readiness: " ^ name)
  end) (DB.thms "abiNativeComplexPrefixReady")
