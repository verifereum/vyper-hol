(* TOP-LEVEL: the real parent cursor record covers its suffix store and
   protects its loaded value during a static recursive child. *)
Theory abiNativeCursorFrame
Ancestors
  abiNativeCursor abiNativeReadFrame abiNativeEncodingDefs abiAllocatedWindows abiAllocationWindows
  abiMemoryFrameCover abiMemoryFrame memoryReadProps compileAllocaProvenance
  compileEnv venomMemDefs venomState finite_map list pair words arithmetic

Theorem abi_native_cursor_stores_cover:
  !func root_cs root_after counter_inst dyn_addr cs ss root_dst root_payload head_base.
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    w2n (root_dst:bytes32) <= head_base /\
    head_base + 32 <= w2n root_dst + LENGTH (root_payload:word8 list) ==>
    abi_writes_cover ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) ss)
      [(head_base,32);(w2n dyn_addr,32)]
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_cursor_def] >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_allocated_window_def]) >>
  rename1 `FLOOKUP ss.vs_allocas counter_inst.inst_id = SOME (cursor_base,cursor_capacity)` >>
  simp_tac bool_ss [abi_writes_cover_def, MEM] >>
  MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> strip_tac
  >| [gvs[] >> qexistsl_tac [`w2n root_dst`, `LENGTH root_payload`] >> simp[],
      gvs[] >> qexistsl_tac [`cursor_base`, `cursor_capacity`] >> conj_tac
      >- (simp_tac bool_ss [MEM] >> disj2_tac >>
          simp_tac bool_ss [abi_allocation_windows_member] >>
          qexists_tac `counter_inst.inst_id` >> simp[]) >>
      rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]]
QED

Theorem abi_native_cursor_static_read:
  !ctx func root_cs root_after counter_inst dyn_addr cs ss mid ret dst_addr payload out target_id.
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    fn_inst_ids_distinct func /\ cs_extends cs mid /\ fn_has_code cs mid func /\
    abi_native_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload ss out /\
    alloca_inv ss /\ abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload) /\
    counter_inst.inst_id <> target_id ==>
    mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_cursor_local_exclusion >> DISCH_TAC >>
  qpat_x_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr`, `payload`, `ss`, `out`,
    `counter_inst.inst_id`, `w2n dyn_addr`, `32`, `target_id`]
    mp_tac abi_native_result_owned_read >> impl_tac >- simp[EQ_SYM_EQ] >> DISCH_TAC >>
  asm_simp_tac bool_ss [mload_read_memory]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual parent cursor store/read frames: " ^ name)
  end) (DB.thms "abiNativeCursorFrame")
