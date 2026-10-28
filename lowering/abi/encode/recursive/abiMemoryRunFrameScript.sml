(* TOP-LEVEL: actual encoder executions preserve all recursive source
   observations in separated windows, so subsequent child calls reuse the
   original source relation. Scratch windows participate in separation. *)
Theory abiMemoryRunFrame
Ancestors
  abiMemoryLeafRun abiMemoryEncodingFrame abiMemoryFrame abiWriterFrame
  memoryReadProps valueEncoding venomState list arithmetic

Theorem abi_encoding_result_source_window:
  !ctx func cs cs' ret dst_addr payload scratch before after offset span.
    abi_encoding_result ctx func cs cs' ret dst_addr payload scratch before after /\
    EVERY (\(write_base,write_count).
      abi_window_separated offset span write_base write_count)
      ((w2n dst_addr,LENGTH payload)::scratch) ==>
    mem_bytes_at offset span before.vs_memory = mem_bytes_at offset span after.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  fs[abi_encoding_result_def] >>
  qspecl_then [`(w2n dst_addr,LENGTH payload)::scratch`, `before`, `after`, `offset`, `span`]
    mp_tac abi_memory_frame_read >> impl_tac >- simp[] >>
  simp[read_memory_eq_mem_bytes_at]
QED

Theorem abi_encoding_result_source:
  !ctx func cs cs' ret dst_addr payload scratch before after info offset span source_bytes.
    abi_encoding_result ctx func cs cs' ret dst_addr payload scratch before after /\
    abi_memory_encoding info offset span before.vs_memory source_bytes /\
    EVERY (\(write_base,write_count).
      abi_window_separated offset span write_base write_count)
      ((w2n dst_addr,LENGTH payload)::scratch) ==>
    abi_memory_encoding info offset span after.vs_memory source_bytes
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encoding_result_source_window >> DISCH_TAC >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >>
  disch_then (qspec_then `after.vs_memory` mp_tac) >> simp[]
QED

Theorem abi_encoding_result_fields:
  !ctx func cs cs' ret dst_addr payload scratch before after entries offset span fields.
    abi_encoding_result ctx func cs cs' ret dst_addr payload scratch before after /\
    abi_memory_fields entries offset span before.vs_memory fields /\
    EVERY (\(write_base,write_count).
      abi_window_separated offset span write_base write_count)
      ((w2n dst_addr,LENGTH payload)::scratch) ==>
    abi_memory_fields entries offset span after.vs_memory fields
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encoding_result_source_window >> DISCH_TAC >>
  drule (CONJUNCT2 abi_memory_encoding_frame) >>
  disch_then (qspec_then `after.vs_memory` mp_tac) >> simp[]
QED

Theorem abi_memory_encoding_writer_frame:
  !writers before after info offset span payload.
    abi_writer_frame writers before after /\
    abi_writer_separated writers after offset span /\
    abi_memory_encoding info offset span before.vs_memory payload ==>
    abi_memory_encoding info offset span after.vs_memory payload
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_writer_frame_read >>
  simp_tac bool_ss [read_memory_eq_mem_bytes_at] >> DISCH_TAC >>
  drule (CONJUNCT1 abi_memory_encoding_frame) >>
  disch_then (qspec_then `after.vs_memory` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI execution source frames: " ^ name)
  end) (DB.thms "abiMemoryRunFrame")
