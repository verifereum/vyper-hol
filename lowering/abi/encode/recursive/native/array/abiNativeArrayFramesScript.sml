(* TOP-LEVEL: individual array writes fit their enclosing output arena
   and actual cursor allocation record. Cached profile windows depend only
   on allocation observations, so pure loop effects preserve them. *)
Theory abiNativeArrayFrames
Ancestors
  abiNativeCursor abiAllocatedWindows abiAllocationWindows abiAllocatorState abiMemoryFrameCover abiMemoryFrame
  compileAllocaProvenance compileEnv venomState finite_map list rich_list words arithmetic

Theorem abi_native_array_write_frame:
  !dst_base payload_len child_base child_len counter_base before after.
    dst_base <= child_base /\ child_base + child_len <= dst_base + payload_len /\
    abi_memory_frame [(child_base,child_len);(counter_base,32)] before after ==>
    abi_memory_frame [(dst_base,payload_len);(counter_base,32)] before after
Proof
  rpt gen_tac >> strip_tac >> irule abi_memory_frame_cover >>
  qexists_tac `[(child_base,child_len);(counter_base,32)]` >> conj_tac
  >- (simp_tac bool_ss [abi_writes_cover_def, MEM] >>
      MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> strip_tac
      >| [gvs[] >> qexistsl_tac [`dst_base`, `payload_len`] >> simp[],
          gvs[] >> qexistsl_tac [`counter_base`, `32`] >> simp[]]) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_array_counter_frame:
  !func root_cs root_after counter_inst counter_addr loop_cs recorded dst_addr payload before after.
    abi_native_cursor func root_cs root_after counter_inst counter_addr loop_cs recorded /\
    abi_memory_frame [(w2n (dst_addr:bytes32),LENGTH (payload:word8 list));(w2n counter_addr,32)] before after ==>
    abi_memory_frame ((w2n dst_addr,LENGTH payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) recorded) before after
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qpat_x_assum `abi_allocated_window _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP recorded.vs_allocas counter_inst.inst_id = SOME (cursor_base,cursor_capacity)` >>
  irule abi_memory_frame_cover >> qexists_tac `[(w2n dst_addr,LENGTH payload);(w2n counter_addr,32)]` >> conj_tac
  >- (simp_tac bool_ss [abi_writes_cover_def, MEM] >>
      MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> strip_tac
      >| [gvs[] >> qexistsl_tac [`w2n dst_addr`, `LENGTH payload`] >> simp[],
          gvs[] >> qexistsl_tac [`cursor_base`, `cursor_capacity`] >> conj_tac
          >- (simp_tac bool_ss [MEM] >> disj2_tac >>
              simp_tac bool_ss [abi_allocation_windows_member] >> qexists_tac `counter_inst.inst_id` >> simp[]) >>
          rpt conj_tac >> first_assum MATCH_ACCEPT_TAC]) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_allocation_windows_allocator_state:
  !ids before after.
    abi_allocator_state after = abi_allocator_state before ==>
    abi_allocation_windows ids after = abi_allocation_windows ids before
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  irule abi_allocation_windows_fields >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_memory_frame_memory_eq:
  !writes before after image.
    after.vs_memory = image.vs_memory ==>
    (abi_memory_frame writes before after <=> abi_memory_frame writes before image)
Proof
  simp[abi_memory_frame_def, read_memory_def]
QED

Theorem abi_memory_frame_reverse:
  !writes before after.
    abi_memory_frame (REVERSE writes) before after <=> abi_memory_frame writes before after
Proof
  simp[abi_memory_frame_def, EVERY_REVERSE]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native array write frames: " ^ name)
  end) (DB.thms "abiNativeArrayFrames")
