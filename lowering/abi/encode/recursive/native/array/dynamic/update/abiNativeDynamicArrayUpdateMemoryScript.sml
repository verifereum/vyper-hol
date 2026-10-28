(* TOP-LEVEL: the real latch preserves every read outside its index cell.
   Separately allocated head, tail and index cells therefore have the exact
   values written by the actual update instructions. *)
Theory abiNativeDynamicArrayUpdateMemory
Ancestors
  abiDynamicLoopUpdate abiDynamicLoopLatch abiChildFrames abiChildSuffix abiMemoryFrame memoryReadProps
  compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_latch_read:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss offset read_len.
    abi_window_separated offset read_len (w2n counter_addr) 32 ==>
    read_memory offset read_len (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) =
      read_memory offset read_len (abi_child_suffix_state mid.cs_next_var head_addr dyn_addr tail_offset child_size ss)
Proof
  rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`[(w2n counter_addr,32)]`,
    `(abi_child_suffix_state mid.cs_next_var head_addr dyn_addr tail_offset child_size ss) with vs_inst_idx := LENGTH mid.cs_current_insts + 3`,
    `abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss`, `offset`, `read_len`]
    mp_tac abi_memory_frame_read >>
  impl_tac >- simp[abi_dynamic_loop_update_state_def, abi_dynamic_loop_latch_memory_frame] >>
  simp[read_memory_def]
QED

Theorem abi_native_dynamic_array_update_words:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss.
    regions_disjoint (w2n head_addr) 32 (w2n dyn_addr) 32 /\
    regions_disjoint (w2n head_addr) 32 (w2n counter_addr) 32 /\
    regions_disjoint (w2n dyn_addr) 32 (w2n counter_addr) 32 ==>
    mload (w2n head_addr) (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) = tail_offset /\
    mload (w2n dyn_addr) (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) = tail_offset + child_size /\
    mload (w2n counter_addr) (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) = index + 1w
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`mid.cs_next_var`, `head_addr`, `dyn_addr`, `tail_offset`, `child_size`, `ss`]
    mp_tac abi_child_suffix_words >> impl_tac >- fs[compileEnvTheory.regions_disjoint_def] >> strip_tac >>
  `!offset. abi_window_separated offset 32 (w2n counter_addr) 32 ==>
    mload offset (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) =
      mload offset (abi_child_suffix_state mid.cs_next_var head_addr dyn_addr tail_offset child_size ss)` by
    (rpt gen_tac >> DISCH_TAC >>
     qspecl_then [`mid`, `head_addr`, `dyn_addr`, `counter_addr`, `index`, `tail_offset`, `child_size`, `ss`, `offset`, `32`]
       mp_tac abi_native_dynamic_array_latch_read >> impl_tac >- first_assum MATCH_ACCEPT_TAC >>
     simp_tac bool_ss [mload_read_memory]) >>
  rpt conj_tac
  >- (first_x_assum (qspec_then `w2n head_addr` mp_tac) >> simp[abi_window_separated_def])
  >- (first_x_assum (qspec_then `w2n dyn_addr` mp_tac) >> simp[abi_window_separated_def]) >>
  simp[abi_dynamic_loop_update_counter]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed exact dynamic array update word values: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayUpdateMemory")
