(* TOP-LEVEL: the actual head/tail update and latch append one complete
   dynamic field, advance its tail counter and increment its index cell. *)
Theory abiNativeDynamicArrayUpdateLayout
Ancestors
  abiNativeDynamicArrayStoreLayout abiNativeDynamicArrayStoreSeparation abiNativeDynamicArrayUpdateMemory
  abiDynamicLoopUpdate abiAllocatedSubwindows abiAllocatedWindows abiFieldMemory abiFieldCompose abiFieldLayoutDefs
  memoryReadProps compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_update_layout:
  !mid head_addr dyn_addr counter_addr index ss target_id dyn_id index_id arena capacity done tail_start payload.
    alloca_inv ss /\ abi_allocated_window ss target_id arena capacity /\
    abi_allocated_window ss dyn_id (w2n dyn_addr) 32 /\ abi_allocated_window ss index_id (w2n counter_addr) 32 /\
    target_id <> dyn_id /\ target_id <> index_id /\ dyn_id <> index_id /\
    w2n head_addr = arena + abi_field_head_size done /\
    abi_field_head_size done + 32 <= tail_start /\ tail_start + abi_field_tail_size done + LENGTH payload <= capacity /\
    abi_fields_layout done arena 0 tail_start ss /\
    read_memory (arena + tail_start + abi_field_tail_size done) (LENGTH payload) ss = payload ==>
    let out = abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index
      (n2w (tail_start + abi_field_tail_size done)) (n2w (LENGTH payload)) ss in
    abi_fields_layout (done ++ [(T,payload)]) arena 0 tail_start out /\
    mload (w2n dyn_addr) out = n2w (tail_start + abi_field_tail_size done + LENGTH payload) /\
    mload (w2n counter_addr) out = index + 1w
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_allocated_window ss target_id (w2n head_addr) 32` by
    (qspecl_then [`ss`, `target_id`, `arena`, `capacity`, `w2n head_addr`, `32`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp_tac bool_ss []) >>
  drule_all abi_native_dynamic_array_store_regions >> strip_tac >>
  qspecl_then [`mid`, `head_addr`, `dyn_addr`, `counter_addr`, `index`, `n2w (tail_start + abi_field_tail_size done)`,
    `n2w (LENGTH payload)`, `ss`] mp_tac abi_native_dynamic_array_update_words >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`mid`, `head_addr`, `dyn_addr`, `counter_addr`, `index`, `n2w (tail_start + abi_field_tail_size done)`,
    `n2w (LENGTH payload)`, `ss`, `target_id`, `dyn_id`, `index_id`, `arena`, `capacity`, `done`, `tail_start`, `payload`]
    mp_tac abi_native_dynamic_array_store_layout >> impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> strip_tac >>
  `mload (arena + abi_field_head_size done)
    (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index
      (n2w (tail_start + abi_field_tail_size done)) (n2w (LENGTH payload)) ss) = n2w (tail_start + abi_field_tail_size done)` by
    (qpat_assum `w2n head_addr = arena + abi_field_head_size done` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (PURE_REWRITE_TAC [abi_fields_layout_append, abi_fields_layout_single, abi_field_head_def, abi_field_tail_def] >>
      asm_simp_tac (srw_ss()) [read_memory_word, ADD_ASSOC]) >>
  asm_simp_tac (srw_ss()) [word_add_n2w]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array field append and counter advance: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayUpdateLayout")
