(* TOP-LEVEL: the precise output/index frame preserves a separate owned
   parent counter, using allocation identities rather than address ordering. *)
Theory abiNativeArrayReadFrame
Ancestors
  abiAllocatedWindows abiAllocatedSeparation abiMemoryFrame compileEnv venomMemDefs venomState list pair words

Theorem abi_native_array_counter_preserved:
  !ss out parent_id target_id counter_id parent_addr dst_addr payload counter_addr.
    alloca_inv ss /\ parent_id <> target_id /\ parent_id <> counter_id /\
    abi_allocated_window ss parent_id (w2n (parent_addr:bytes32)) 32 /\
    abi_allocated_window ss target_id (w2n (dst_addr:bytes32)) (LENGTH (payload:word8 list)) /\
    abi_allocated_window ss counter_id (w2n (counter_addr:bytes32)) 32 /\
    abi_memory_frame [(w2n dst_addr,LENGTH payload);(w2n counter_addr,32)] ss out ==>
    mload (w2n parent_addr) out = mload (w2n parent_addr) ss
Proof
  rpt gen_tac >> strip_tac >> `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  qspecl_then [`ss`, `[(target_id,(w2n dst_addr,LENGTH payload));(counter_id,(w2n counter_addr,32))]`,
    `parent_id`, `w2n parent_addr`, `32`] mp_tac abi_allocated_windows_separated >>
  impl_tac >- asm_simp_tac bool_ss [EVERY_DEF, FST, SND, EQ_SYM_EQ] >>
  simp_tac bool_ss [MAP, SND] >> DISCH_TAC >>
  qspecl_then [`[(w2n dst_addr,LENGTH payload);(w2n counter_addr,32)]`, `ss`, `out`, `w2n parent_addr`]
    mp_tac abi_memory_frame_mload >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

Theorem abi_native_array_parent_regions:
  !ss source_id target_id parent_id source_base source_capacity dst_base payload_len parent_base.
    alloca_inv ss /\ parent_id <> source_id /\ parent_id <> target_id /\
    abi_allocated_window ss source_id source_base source_capacity /\ 32 <= source_capacity /\
    abi_allocated_window ss target_id dst_base payload_len /\ 32 <= payload_len /\
    abi_allocated_window ss parent_id parent_base 32 ==>
    regions_disjoint source_base 32 parent_base 32 /\ regions_disjoint parent_base 32 dst_base 32
Proof
  rpt gen_tac >> strip_tac >> `allocas_non_overlapping ss` by fs[alloca_inv_def] >>
  `abi_allocated_window ss source_id source_base 32` by
    (qspecl_then [`ss`, `source_id`, `source_base`, `source_capacity`, `32`]
       mp_tac abi_allocated_window_shrink >> simp[]) >>
  `abi_allocated_window ss target_id dst_base 32` by
    (qspecl_then [`ss`, `target_id`, `dst_base`, `payload_len`, `32`]
       mp_tac abi_allocated_window_shrink >> simp[]) >>
  conj_tac
  >- (qspecl_then [`ss`, `(source_id,(source_base,32))`, `(parent_id,(parent_base,32))`]
        mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[EQ_SYM_EQ] >> simp[]) >>
  qspecl_then [`ss`, `(parent_id,(parent_base,32))`, `(target_id,(dst_base,32))`]
    mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned native array parent counter read: " ^ name)
  end) (DB.thms "abiNativeArrayReadFrame")
