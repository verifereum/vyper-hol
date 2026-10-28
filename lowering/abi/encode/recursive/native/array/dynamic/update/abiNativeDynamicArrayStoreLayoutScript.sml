(* TOP-LEVEL: the actual three stores preserve all completed output and
   the newly encoded child bytes. Allocation identities discharge both
   counter writes; the head write uses its exact interval in the arena. *)
Theory abiNativeDynamicArrayStoreLayout
Ancestors
  abiNativeDynamicArrayStoreSeparation abiDynamicLoopUpdate abiAllocatedSubwindows abiAllocatedWindows
  abiFieldMemory abiFieldLayoutDefs abiMemoryFrame compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_store_layout:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss target_id dyn_id index_id arena capacity done tail_start payload.
    alloca_inv ss /\ abi_allocated_window ss target_id arena capacity /\
    abi_allocated_window ss dyn_id (w2n dyn_addr) 32 /\ abi_allocated_window ss index_id (w2n counter_addr) 32 /\
    dyn_id <> target_id /\ index_id <> target_id /\
    w2n head_addr = arena + abi_field_head_size done /\
    abi_field_head_size done + 32 <= tail_start /\ tail_start + abi_field_tail_size done + LENGTH payload <= capacity /\
    abi_fields_layout done arena 0 tail_start ss /\
    read_memory (arena + tail_start + abi_field_tail_size done) (LENGTH payload) ss = payload ==>
    abi_fields_layout done arena 0 tail_start
      (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) /\
    read_memory (arena + tail_start + abi_field_tail_size done) (LENGTH payload)
      (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) = payload
Proof
  rpt gen_tac >> strip_tac >>
  `abi_allocated_window ss target_id (w2n head_addr) 32` by
    (qspecl_then [`ss`, `target_id`, `arena`, `capacity`, `w2n head_addr`, `32`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp_tac bool_ss []) >>
  qspecl_then [`mid`, `head_addr`, `dyn_addr`, `counter_addr`, `index`, `tail_offset`, `child_size`, `ss`,
    `target_id`, `dyn_id`, `index_id`, `arena`, `capacity`] ASSUME_TAC abi_native_dynamic_array_store_read >>
  qpat_assum `!read_offset read_len. _` (qspecl_then [`arena`, `abi_field_head_size done`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >> decide_tac) >> DISCH_TAC >>
  qpat_assum `!read_offset read_len. _` (qspecl_then [`arena + tail_start`, `abi_field_tail_size done`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >> decide_tac) >> DISCH_TAC >>
  qpat_assum `!read_offset read_len. _` (qspecl_then [`arena + tail_start + abi_field_tail_size done`, `LENGTH payload`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >> decide_tac) >> DISCH_TAC >>
  conj_tac
  >- (qpat_x_assum `abi_fields_layout _ _ _ _ ss` (mp_tac o PURE_REWRITE_RULE [abi_fields_layout_def]) >>
      asm_simp_tac bool_ss [abi_fields_layout_def, ADD_0]) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed completed output and child bytes through actual array stores: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStoreLayout")
