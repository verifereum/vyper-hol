(* TOP-LEVEL: derive physical separation from allocation identities. Writes
   within the reader's own allocation need only their local interval check. *)
Theory abiAllocatedSeparation
Ancestors
  abiAllocatedWindows abiMemoryFrame compileEnv venomMemDefs venomState list pair

Theorem abi_allocated_window_separated:
  !ss read_id read_offset read_len write_id write_offset write_len.
    allocas_non_overlapping ss /\
    abi_allocated_window ss read_id read_offset read_len /\
    abi_allocated_window ss write_id write_offset write_len /\
    (write_id = read_id ==> abi_window_separated read_offset read_len write_offset write_len) ==>
    abi_window_separated read_offset read_len write_offset write_len
Proof
  rpt gen_tac >> strip_tac >> Cases_on `write_id = read_id` >- fs[] >>
  mp_tac (Q.SPECL [`ss`, `(read_id,(read_offset,read_len))`, `(write_id,(write_offset,write_len))`]
    abi_allocated_window_disjoint) >> impl_tac >- simp[EQ_SYM_EQ] >>
  simp[abi_window_separated_def]
QED

Theorem abi_allocated_windows_separated:
  !ss windows read_id read_offset read_len.
    allocas_non_overlapping ss /\ abi_allocated_window ss read_id read_offset read_len /\
    EVERY (\window. abi_allocated_window ss (FST window) (FST (SND window)) (SND (SND window))) windows /\
    EVERY (\window. FST window = read_id ==>
      abi_window_separated read_offset read_len (FST (SND window)) (SND (SND window))) windows ==>
    EVERY (\(write_offset,write_len). abi_window_separated read_offset read_len write_offset write_len)
      (MAP SND windows)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [EVERY_MAP, EVERY_MEM, FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`write_id`, `write_offset`, `write_len`] >> DISCH_TAC >>
  `abi_allocated_window ss write_id write_offset write_len` by
    (qpat_x_assum `EVERY (\window. abi_allocated_window _ _ _ _) windows`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(write_id,(write_offset,write_len))` mp_tac) >> simp[]) >>
  `write_id = read_id ==> abi_window_separated read_offset read_len write_offset write_len` by
    (qpat_x_assum `EVERY (\window. FST window = read_id ==> _) windows`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(write_id,(write_offset,write_len))` mp_tac) >> simp[]) >>
  drule_all abi_allocated_window_separated >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-derived window separation: " ^ name)
  end) (DB.thms "abiAllocatedSeparation")
