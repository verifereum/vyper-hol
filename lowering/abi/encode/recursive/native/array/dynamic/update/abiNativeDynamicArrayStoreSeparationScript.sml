(* TOP-LEVEL: allocation identities separate both loop cells from output
   reads. Only the new head word lies in the output allocation, so its
   local interval check suffices for all three actual update writes. *)
Theory abiNativeDynamicArrayStoreSeparation
Ancestors
  abiAllocatedWindows abiAllocatedSubwindows abiAllocatedSeparation abiMemoryFrame abiDynamicLoopUpdate
  compileEnv venomMemDefs venomState list pair words arithmetic

Theorem abi_native_dynamic_array_store_reads:
  !ss target_id dyn_id index_id read_offset read_len head_addr dyn_addr counter_addr.
    allocas_non_overlapping ss /\ abi_allocated_window ss target_id read_offset read_len /\
    abi_allocated_window ss target_id (w2n (head_addr:bytes32)) 32 /\
    abi_allocated_window ss dyn_id (w2n (dyn_addr:bytes32)) 32 /\
    abi_allocated_window ss index_id (w2n (counter_addr:bytes32)) 32 /\
    dyn_id <> target_id /\ index_id <> target_id /\ abi_window_separated read_offset read_len (w2n head_addr) 32 ==>
    EVERY (\(base,count). abi_window_separated read_offset read_len base count)
      [(w2n head_addr,32);(w2n dyn_addr,32);(w2n counter_addr,32)]
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ss`, `[(target_id,(w2n head_addr,32));(dyn_id,(w2n dyn_addr,32));(index_id,(w2n counter_addr,32))]`,
    `target_id`, `read_offset`, `read_len`] mp_tac abi_allocated_windows_separated >>
  impl_tac >- asm_simp_tac bool_ss [EVERY_DEF, FST, SND] >> simp_tac bool_ss [MAP, SND]
QED

Theorem abi_native_dynamic_array_store_regions:
  !ss target_id dyn_id index_id head_addr dyn_addr counter_addr.
    alloca_inv ss /\ target_id <> dyn_id /\ target_id <> index_id /\ dyn_id <> index_id /\
    abi_allocated_window ss target_id (w2n (head_addr:bytes32)) 32 /\
    abi_allocated_window ss dyn_id (w2n (dyn_addr:bytes32)) 32 /\
    abi_allocated_window ss index_id (w2n (counter_addr:bytes32)) 32 ==>
    regions_disjoint (w2n head_addr) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n head_addr) 32 (w2n counter_addr) 32 /\
    regions_disjoint (w2n dyn_addr) 32 (w2n counter_addr) 32
Proof
  rpt gen_tac >> strip_tac >> `allocas_non_overlapping ss` by fs[alloca_inv_def] >> rpt conj_tac
  >- (qspecl_then [`ss`, `(target_id,(w2n head_addr,32))`, `(dyn_id,(w2n dyn_addr,32))`]
        mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[])
  >- (qspecl_then [`ss`, `(target_id,(w2n head_addr,32))`, `(index_id,(w2n counter_addr,32))`]
        mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[]) >>
  qspecl_then [`ss`, `(dyn_id,(w2n dyn_addr,32))`, `(index_id,(w2n counter_addr,32))`]
    mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[]
QED

Theorem abi_native_dynamic_array_store_read:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss target_id dyn_id index_id arena capacity read_offset read_len.
    alloca_inv ss /\ abi_allocated_window ss target_id arena capacity /\
    abi_allocated_window ss target_id (w2n (head_addr:bytes32)) 32 /\
    abi_allocated_window ss dyn_id (w2n (dyn_addr:bytes32)) 32 /\
    abi_allocated_window ss index_id (w2n (counter_addr:bytes32)) 32 /\
    dyn_id <> target_id /\ index_id <> target_id /\
    arena <= read_offset /\ read_offset + read_len <= arena + capacity /\
    abi_window_separated read_offset read_len (w2n head_addr) 32 ==>
    read_memory read_offset read_len (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) =
      read_memory read_offset read_len ss
Proof
  rpt gen_tac >> strip_tac >> `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `abi_allocated_window ss target_id read_offset read_len` by
    (qspecl_then [`ss`, `target_id`, `arena`, `capacity`, `read_offset`, `read_len`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []) >>
  qspecl_then [`ss`, `target_id`, `dyn_id`, `index_id`, `read_offset`, `read_len`, `head_addr`, `dyn_addr`, `counter_addr`]
    mp_tac abi_native_dynamic_array_store_reads >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`[(w2n head_addr,32);(w2n dyn_addr,32);(w2n counter_addr,32)]`, `ss`,
    `abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss`, `read_offset`, `read_len`]
    mp_tac abi_memory_frame_read >> impl_tac >- simp[abi_dynamic_loop_update_frame] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-based actual array update read separation: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStoreSeparation")
