(* TOP-LEVEL: allocation identities discharge memory-frame separation for
   every read window backed by an allocation different from all writers. *)
Theory abiAllocatedMemoryFrame
Ancestors
  abiAllocatedWindows abiMemoryFrame compileEnv venomMemDefs venomState list pair

Theorem abi_allocated_memory_frame_read:
  !allocation_ss before after windows read_id read_offset read_len.
    allocas_non_overlapping allocation_ss /\
    abi_allocated_window allocation_ss read_id read_offset read_len /\
    EVERY (\window. abi_allocated_window allocation_ss (FST window) (FST (SND window)) (SND (SND window)) /\
      FST window <> read_id) windows /\
    abi_memory_frame (MAP SND windows) before after ==>
    read_memory read_offset read_len after = read_memory read_offset read_len before
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`MAP SND (windows:(num # (num # num)) list)`, `before`, `after`, `read_offset`, `read_len`]
    abi_memory_frame_read) >> impl_tac >- (
    conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    simp_tac (srw_ss()) [EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
    MAP_EVERY qx_gen_tac [`write_id`, `write_offset`, `write_count`] >> DISCH_TAC >>
    `abi_allocated_window allocation_ss write_id write_offset write_count /\ write_id <> read_id` by
      (qpat_x_assum `EVERY _ windows` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
       disch_then (qspec_then `(write_id,(write_offset,write_count))` mp_tac) >> simp[]) >>
    mp_tac (Q.SPECL [`allocation_ss`, `(read_id,(read_offset,read_len))`, `(write_id,(write_offset,write_count))`]
      abi_allocated_window_disjoint) >> impl_tac >- simp[EQ_SYM_EQ] >> simp[abi_window_separated_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-derived memory-frame reads: " ^ name)
  end) (DB.thms "abiAllocatedMemoryFrame")
